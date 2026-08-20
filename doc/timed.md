# Timed (metric) operators: design

How DejaVuMT implements `S[a,b]`, `S[a,*]`, `Z[..]`, `P[..]`, `H[..]` and
the sugar `[<=n] [<n] [>=n] [>n]`. Companion to the "Metric Operators" section of the
paper; this note is the implementation view.

## Timed traces

A timed trace attaches to every event an absolute, non-decreasing integer
timestamp `T` — in the CSV log, the last column of each line (DejaVu's
format): `open,a,17` is `open(a)` at time 17. Timed operators speak about the
**age** of a past event: current timestamp minus the timestamp of the
witnessing occurrence.

    phi S[a,b] psi   --  psi held between a and b time units ago,
                         and phi has held at every step since.

Semantically `P[a,b] phi = true S[a,b] phi` and `H[a,b] phi = !P[a,b]!phi`.
`Z` (*zince*) is since with a strictly-past witness: `phi Z psi` = "psi held
strictly in the past and phi has held since, through now" =
`phi & @(phi S psi)`; its timed form stamps the witness with the *previous*
event's timestamp.  DejaVu provides only `Z[<=n]`; the untimed `Z` and the
general `Z[a,b]` are DejaVuMT extensions.  (DejaVu's Z recurrence keeps only
the most recent witness — equivalent for `[<=n]`, where the newest witness is
always the freshest, but not for a general interval, where an older witness
can be in the window while the newest is still too young; DejaVuMT therefore
keeps all witnesses, which coincides with DejaVu on `[<=n]`.)
The upper bound may be `*` (absent). With integer time the comparison forms
are sugar: `[<=n]=[0,n]`, `[<n]=[0,n-1]`, `[>=n]=[n,*]`, `[>n]=[n+1,*]`. The
unconstrained interval `[0,*]` is exactly the untimed `S`.

Although Z, P and H are *defined* by these rewrites, the engine does not
compile them that way: every surface operator (S, Z, P, H — timed and untimed)
gets its
own node interpreting its own (provably equal) recurrence, so the debug tree
mirrors the specification one-to-one, with no encoding artifacts (no
constant-`true` child under P, no `¬P¬` chain for H). For P the recurrence is
the stamped since-recurrence with the phi-conjunct dropped. For H the node
stores the record-set of phi's *failures* — the state of `P[a,b]!phi`, which
starts at `false` = "no failure yet" = vacuously true — and exports the
*negation* of its projection; so an H node's displayed state describes
`!phi`, while its displayed value describes `phi`.

## The state: records with a timestamp

An untimed `phi S psi` node stores one formula over its free data variables,
updated by the recurrence

    S  <-  B[psi]  or  (B[phi] and pre[S]).

The timed node must remember not only *that* a witnessing `psi` occurred but
*when*. Its stored state is the same formula extended with **one integer
variable `t`** (one fresh constant per timed node, e.g. `_t3`, with exactly
the same status as the data variables), and the recurrence stamps the current
timestamp onto the new disjunct:

    S  <-  (B[psi] and t = T)  or  (B[phi] and pre[S]).

A satisfying assignment of `S` is a **record**: "psi held for these data
values at time t, and phi has held since". Think of `S` as a table:

    x = "a"  and  t = 0        -- p(a) was observed at time 0
    x = "b"  and  t = 3        -- p(b) was observed at time 3

Two properties make this efficient:

- **Records are immutable.** A record `t = 0` is written once and never
  rewritten. There is no per-step aging update (DejaVu, by contrast, adds the
  time delta to every stored age at every step, with a bit-level adder built
  from BDD operations). It is the *query* that moves: the window constraint
  `a <= T - t <= b` is evaluated against the current timestamp `T`.

- **The two window bounds behave differently.**
  The *upper* bound is monotone — a record older than `b` stays older than
  `b` forever — so expired records can be deleted from the state
  (`prune_expired` in `backend.py` replaces `t = c` atoms with `c < T - b` by
  `false`, in and/or positions only). The state thus holds at most the last
  `b` time units of records.
  The *lower* bound is **not** monotone — a record that is too young will
  mature into the window later — so it is applied only in the value query,
  never to the state.

- **No upper bound (`[a,*]`)**: nothing expires, but a record past the lower
  bound satisfies the window forever, so its timestamp has become
  irrelevant: the engine projects `t` away from the matured part
  (`Exists t . S and T - t >= a`, quantifier-eliminated), merging all matured
  records into one time-free formula that thereafter evolves like ordinary
  untimed state. This is the SMT analogue of DejaVu's saturation of ages at
  `n+1`. So DejaVu's two state-bounding devices are the two halves of the
  window: the upper bound *prunes* records, the lower bound *anonymizes*
  them.

## State vs. exported value

The node's stored state mentions `t`, but what the enclosing formula needs is
an ordinary formula over the data variables. The node therefore **exports**
the time-free projection

    value  =  QElim( Exists t . S  and  a <= T - t <= b )

where `QElim` is quantifier elimination (exact for linear integer
arithmetic). Here a node's stored formula and its exported value differ (the
H nodes are the other such place: failure records in, negation out); for all
other operators the two coincide. In the code the entire difference is one
accessor: enclosing nodes
read a child through its exported value (`nowval`/`preval` in `engine.py`)
instead of reading the stored slot (`now`/`pre`) directly; for untimed nodes
the two share one object. Because the exported value is time-free, timed
operators compose with everything — negation, quantifiers, other temporal
operators — and *nested* timed operators just use distinct, locally
eliminated time variables.

## The evolution of an example

Spec (`examples/timed/prop.qtl`):

    pred open(f: String)
    pred close(f: String)
    prop timely : Forall f . close(f) -> P[<=5] open(f)

Log (`examples/timed/log.csv`): `open(a)@0, close(a)@3, open(b)@4,
close(b)@12`. Actual `debug` output (the unlabeled annotation on each node is its stored
slot; where the exported value differs — timed and H nodes — it follows,
labeled `value:`):

    ----- event 1: open(a) @ 0 -----

    ∀ f . (close(f) → P[<=5] open(f))  true
    └─ (close(f) → P[<=5] open(f))  true
       ├─ close(f)  false
       └─ P[<=5] open(f)  (f = "a" ∧ 0 = _t1)   value: f = "a"
          └─ open(f)  f = "a"

    ----- event 2: close(a) @ 3 -----

    ∀ f . (close(f) → P[<=5] open(f))  true
    └─ (close(f) → P[<=5] open(f))  true
       ├─ close(f)  f = "a"
       └─ P[<=5] open(f)  (f = "a" ∧ 0 = _t1)   value: f = "a"
          └─ open(f)  false

    ----- event 3: open(b) @ 4 -----

    ∀ f . (close(f) → P[<=5] open(f))  true
    └─ (close(f) → P[<=5] open(f))  true
       ├─ close(f)  false
       └─ P[<=5] open(f)  ((f = "b" ∧ 4 = _t1) ∨ (f = "a" ∧ 0 = _t1))   value: (f = "a" ∨ f = "b")
          └─ open(f)  f = "b"

    ----- event 4: close(b) @ 12 -----

    ∀ f . (close(f) → P[<=5] open(f))  false
    └─ (close(f) → P[<=5] open(f))  ¬(f = "b")
       ├─ close(f)  f = "b"
       └─ P[<=5] open(f)  false   value: false
          └─ open(f)  false

Read the timed node's line across the events: the record `f="a" ∧ t=0` is
written at event 1 and *never touched* afterwards; at event 2 (T=3) it is
still in the window (3-0 <= 5) so the exported value is `f="a"` and `close(a)`
is satisfied; at event 3 a second record is added; at event 4 (T=12) both
records have fallen out of the window (12-0 > 5, 12-4 > 5), pruning empties
the state, the exported value is `false`, and `close(b)` violates.

## Contrast with DejaVu

DejaVu bit-blasts time into the BDDs: five groups of time bits (age, new age,
delta, carry, limit), a ripple-carry adder (`addConst`) recomputing every age
at every step, comparator circuits (`gtConst`), saturation via BDD
if-then-else, and a projection plus bit-renaming per step. Here time is one
integer variable per timed node: no aging (records are immutable), the
freshness test is a linear constraint, the projection is one quantifier
elimination. That is also why the *interval* operator `S[a,b]` costs nothing
extra — a second bound is one more inequality in the same query — whereas in
the circuit encoding each bound is compiled hardware; DejaVu accordingly
provides only the one-sided `[<=n]` and `[>n]`, which are the two degenerate
intervals.

Semantics agreement with DejaVu is validated by the differential harness
(`experiments/ab_validate.py`): all comparable timed pairs of the DejaVu
distribution produce identical verdicts (DejaVu decides a log is timed by its
*filename* containing `.timed.` — the harness mirrors this convention).

## Variable bounds

Nothing in the encoding requires `a`, `b` to be literals — the window test
is just a linear constraint with one more free variable. Two cases:

**Symbolic parameters (implemented).** The upper bound may be a parameter
the monitor never fixes (`P[<=n]`), turning each verdict into a constraint
on it ("holds iff n >= 7") — see `doc/parametric.md`. For the past
operators the verdicts come for free (a past verdict is known at its own
position); the price is state: with `n` symbolic neither the expiry pruning
nor the `[a,*]` saturation of this document applies — every record matters
for some `n` — so the node's state grows with the trace.

**Data-dependent bounds (implemented).** A bound may also be a *quantified
variable* — a deadline carried by the trace:

    Forall n . a(n) -> F[0,n] b        -- each a-event brings its own deadline
    Forall d . rsp(d) -> P[0,d] req    -- per-response allowance

The variable must be `Int`. Unlike a parameter, the quantifier discharges
the bound, so verdicts stay Boolean. There is no numeric deadline to close
future windows by; instead the obligation brackets do it — the upper
bracket `Forall n . a(n) -> (q | n >= elapsed)` turns false exactly when
time outruns the carried deadline, so violations are still reported
promptly. As with symbolic bounds, records under a data-dependent window
cannot be pruned or saturated.
