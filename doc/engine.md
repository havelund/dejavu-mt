# How the engine works

A property compiles into an array of **nodes** — its subformula tree in
bottom-up order, `root` last. The two algorithms below — the past
fragment, then the future extension that modifies it in exactly two
places — are the per-property core of `FormulaMonitor.step`/`end` in
`engine.py`; they omit rules
(evaluated in a second pass so that recursion under `@` reads this
position's first pass), state variables, Python functions, parametric
bounds, and the placeholder machinery for *nested* future operators —
each covered in its section below.

## Algorithm 1: the past fragment

Types: `Node` — the property's compiled subformula nodes; `Formula` —
SMT formulas; `Time` — integer timestamps. `QElim` is quantifier
elimination: it rewrites a quantified formula into an equivalent
quantifier-free one (exact over linear integer arithmetic; over strings
it may fail, in which case the quantifier is left in place and the final
SAT check decides). For example, projecting the time variable out of a
stamped record at current timestamp `T = 7`:

    QElim( Exists t . (x = "a" & t = 3) & 7 - t <= 5 )  =  x = "a"

(the record's age is 4, within the bound; had the record been `t = 1`,
the result would be `false`).

    -- State:
    pre, now       : Node -> Formula
        -- node n's STORED state: one formula over the subformula's free
        -- variables, plus a private time variable t at a timed past
        -- node (its stamped records)
    preval, nowval : Node -> Formula
        -- node n's EXPORTED value, the formula its parent reads.  Equal
        -- to the stored state, except: a timed past node exports the
        -- time-free window projection of its records, and an H node --
        -- whose stored records are phi's FAILURES -- exports the
        -- negation of that projection ("no failure in the window")

    pre[n] := false for every n;  pos := 0

    for each event E (with timestamp T):
        pos := pos + 1
        for each node n, bottom-up:
            -- 1. update the stored state by n's recurrence.  Rule:
            --    exports for others, state for self -- children are read
            --    through nowval/preval, a node's own history through
            --    pre[n]
            case n of
              p(x1,..,xk):  now[n] := E's p-facts as a formula:
                            (x1=v1 & .. & xk=vk) | ..      (false if none)
              connective:   now[n] := the operator applied to the
                            children's nowval
              @ phi:        now[n] := preval[phi]
              phi S psi:    now[n] := nowval[psi] | (nowval[phi] & pre[n])
              phi S[a,b] psi:
                            now[n] := bound( (nowval[psi] & t = T)
                                             | (nowval[phi] & pre[n]) )
                            -- Z, P, H with a bound: analogous stamped
                            -- recurrences through the same bound()
              Exists x.phi: now[n] := QElim(Exists x . nowval[phi])
            simplify now[n]
            -- 2. export the value the parent reads:
            nowval[n] := export(n, now[n])
              -- identity, except at a timed past node:
              --   export = QElim(Exists t . now[n] & a <= T - t <= b)
              --   (negated for H: "no failure in the window")
        pre := now;  preval := nowval
        report (pos, SAT(nowval[root]))
            -- root is closed, so SAT decides it:
            -- satisfiable = holds, unsatisfiable = violated

That is the whole monitor for past-time properties: one bottom-up pass of
recurrences per event, one satisfiability check of the closed root. That is
also exactly what the monitor *computes*; how it avoids repeating work that
cannot change anything is described at the end, under *Work the engine
avoids*.

## Algorithm 2: the future extension

Future operators change the algorithm in exactly two places; everything
above stays as it is.

**Change 1 — a new branch in the pass's case analysis.** Algorithm 1's
bottom-up pass dispatches on each node's operator (`case n of ...`);
the future operators add one more branch to that dispatch, given below.
Each node headed by a future operator (`FNode ⊆ Node` is the set of
these) carries new state — a table of stamped observations:

    tab : FNode -> Formula x Formula   (for U)
        | FNode -> Formula             (for F, G, X)
        -- a "table" is ONE formula, read as a relation: its satisfying
        -- assignments are the rows.  Typically it is a disjunction with
        -- one disjunct per row, e.g.
        --     A  =  (x = "a" & s = 2) | (x = "b" & s = 5)
        -- is the table holding runs ("a", 2) and ("b", 5).  For
        -- phi U[a,b] psi there are two such formulas, (A, W), over
        -- different columns, coupled only through the update (a psi
        -- observation adds to W one row per run currently in A).
        -- In the row shapes below, "data" stands for the data columns:
        -- the subformula's free variables (x, u, ...), SMT variables
        -- exactly like s and t2 -- a row assigns concrete values to
        -- all columns at once:
        --   a row (data, s) of A is a live RUN -- phi has held for
        --     these data at every position from position s through the
        --     current one.  Runs are identified by their start POSITION
        --     s: positions are unique, timestamps need not be;
        --   a row (data, s, t2) of W is an ANSWERED run -- the run
        --     begun at position s was still alive when a psi for these
        --     data was observed, at clock value t2.
        -- For F a single table of observed psi's (witnesses), each
        -- stamped with its clock value; for G likewise but recording
        -- the counterexamples (positions where psi failed)

The new branches are shaped like Algorithm 1's: update the state (here
the table), export a value for the parent to read. `clock` is `T`, or
`pos` for the untimed forms.

Two kinds of names appear inside these formulas, and they are not alike:
`s`, `t2`, `t` and the data variables are **SMT variables** — the
table's columns, living in the formulas across events; `pos`, `clock`,
`anchor`, `a`, `b` are **concrete numbers** at the moment a line runs,
inserted as numerals. So `A := A | (s = pos)` executed at position 17
literally adds the disjunct `s = 17`. The data columns end up as
equations in a row too (`x = "a"`), but by a different route: the engine
never writes them itself — they arrive ready-made inside `nowval[psi]`
and `nowval[phi]`, built at the predicate leaves from the event's facts,
and conjoining those values into a row is what writes its data
equations.

The `U` branch, in words, does three things in a deliberate order.
- *Start:* a run begins at this position — the new row has its data
columns unconstrained, because which data values matter is decided by
the later steps, not here. 
- *Answer:* a `psi` in this event answers every
run alive right now; `phi` is required strictly *before* the witness,
not at it, which is why this happens before the phi test — in
particular, the run just started may be answered immediately, with no
`phi` involved. 
- *Survive:* a run that was not answered can only be
answered by a later witness, and for that `phi` must hold now; runs (and
data values) failing `phi` are deleted — the new row included. Deletion
is by conjunction: `A` is a disjunction of rows, so conjoining
`nowval[phi]` distributes over them and filters each row down to the
data values satisfying `phi` — e.g. with `A = (x="a" & s=2) |
(x="b" & s=5)` and `nowval[phi] = (x="a")`, the second row becomes
unsatisfiable and disappears (that run died), the first survives
unchanged.

              phi U[a,b] psi (an FNode, with tab[n] = (A, W)):
                            A := A | (s = pos)                  -- start
                            W := W | (nowval[psi] & A & t2 = clock)
                                                                -- answer
                            A := nowval[phi] & A                -- survive
                            nowval[n] := QElim( Exists s, t2 . W
                                                & s = pos
                                                & a <= t2 - clock <= b )
                                -- the window is measured from the clock
                                -- value of the position being judged --
                                -- here the current one, hence clock.
                                -- Every stored t2 is <= clock, so at
                                -- export only a witness from THIS event
                                -- (t2 = clock, delay 0) can satisfy the
                                -- query: the export really is just
                                -- "proven so far".  Positive delays are
                                -- credited later by CHECK, which re-runs
                                -- this same query for a parked position
                                -- with that position's older clock value
                                -- (its ANCHOR) in place of clock -- the
                                -- stamps exceed THAT.
                                --
                                -- s and t2 are W's column variables:
                                -- they occur in W's rows, e.g.
                                --   W = (x="a" & s=2 & t2=9) | ...
                                -- The two conjuncts constrain them:
                                -- s = pos picks the rows whose run is
                                -- the one started HERE, and
                                -- a <= t2 - clock <= b keeps those
                                -- whose witness lies in the window.
                                -- Each row pins s and t2 to numerals,
                                -- so the two conjuncts act as row
                                -- filters (arithmetic on constants, per
                                -- row), and the Exists/QElim just
                                -- discards the spent columns.  E.g.
                                -- judging position 2, which occurred at
                                -- time 7 (anchor=7), window [0,5]; the
                                -- rows were stamped when their psi's
                                -- arrived (times 9 and 30), and the
                                -- current clock -- at least 30 -- does
                                -- not occur in the query at all:
                                --   W = (x="a" & s=2 & t2=9)
                                --     | (x="b" & s=2 & t2=30)
                                -- row 1: t2-7=2, in the window; row 2:
                                -- t2-7=23, out.  Result: x = "a" -- the
                                -- data values for which the query
                                -- holds.  A LOWER bound on the eventual
                                -- answer, since W can still grow
              F[a,b] psi (an FNode, with tab[n] = S):
                            S := S | (nowval[psi] & t = clock)
                            nowval[n] := QElim( Exists t . S
                                                & a <= t - clock <= b )
                                -- t is S's column variable, occurring
                                -- in S's rows (x="a" & t=9); the
                                -- conjunct keeps rows in the window,
                                -- QElim projects t away, leaving the
                                -- data values for which it holds
              G[a,b] psi:   as F, but S records !psi (counterexamples)
                            and the exported query is negated
              X psi:        as F, stamped by pos, window [1,1]

The export is only what the table proves *so far* — dealing with that
provisionality is Change 2's job.

A note on the stamps, since the subtraction `t2 - anchor` can mislead:
`t2` never exceeds the current clock — rows record the *past*. What a
stamp exceeds is the **anchor** of an older parked position: the delay
`t2 - anchor` is measured from the judged position forward, so it is
`>= 0` for every row written at or after that position.

**A worked trace.** `prop u : Exists x . busy(x) U[0,5] done(x)` on the
timed log `busy(a)@0, busy(a)@2, done(a)@4, busy(b)@9`. The tables have
one data column `x`; recall that a new run's row leaves `x`
unconstrained, and the survive step then narrows it:

    event 1, busy(a) @ 0  (pos 1):
        start:   (A, W) = ( (s=1),           false )   -- new row, any x
        answer:  (A, W) = ( (s=1),           false )   -- no done here
        survive: (A, W) = ( (x="a" & s=1),   false )   -- busy's value
                                                       --   is x="a"
        export: false; position 1 parked (deadline 0+5)

    event 2, busy(a) @ 2  (pos 2):
        start:   (A, W) = ( (x="a" & s=1) | (s=2),            false )
        answer:  (A, W) = ( (x="a" & s=1) | (s=2),            false )
        survive: (A, W) = ( (x="a" & s=1) | (x="a" & s=2),    false )
        export: false; position 2 parked; neither deadline passed

    event 3, done(a) @ 4  (pos 3):
        start:   (A, W) = ( (x="a" & s=1) | (x="a" & s=2) | (s=3),
                            false )
        answer:  (A, W) = ( (x="a" & s=1) | (x="a" & s=2) | (s=3),
                            (x="a" & s=1 & t2=4)
                          | (x="a" & s=2 & t2=4)
                          | (x="a" & s=3 & t2=4) )
                 -- done's value x="a" conjoined with A: one done
                 -- answers all three live runs (the fresh s=3 row
                 -- narrows to x="a" too)
        survive: (A, W) = ( false,  W as above )
                 -- busy is false here (the event is a done): all runs
                 -- die -- but they are answered
        CHECK: position 1 (anchor 0): row s=1, delay 4-0 in [0,5],
                 Exists x: x="a"  -> true
               position 2 (anchor 2): row s=2, delay 2  -> true
               position 3 (anchor 4): row s=3, delay 0  -> true
        all pending resolved; tables cleared: (A, W) = (false, false)

    event 4, busy(b) @ 9  (pos 4):
        start:   (A, W) = ( (s=4),           false )
        answer:  (A, W) = ( (s=4),           false )
        survive: (A, W) = ( (x="b" & s=4),   false )
        export: false; position 4 parked (deadline 9+5 = 14)
        -- the run is alive and the deadline ahead: undecided

    end of trace: the window closes with no witness -- position 4 is
    forced to FALSE ("determined at end of trace").
    Verdicts: 1-3 hold, 4 violated.

**Change 2 — verdict delivery.** The root's value now depends on events
not yet read, so the report line of Algorithm 1 is replaced by
park-and-check over a notebook of open positions (new state):

    pending : Set(Obligation),  Obligation = Pos x Time x (Node -> Formula)
        -- one obligation per position whose verdict is not yet known:
        -- the position, its timestamp (the anchor its time windows are
        -- measured from), and a snapshot of nowval there.  The snapshot
        -- is a copy of the ARRAY only -- formulas are immutable and
        -- shared, so it is one reference per node; its cost is keeping
        -- that position's formulas alive while the obligation pends
        -- (bounded windows bound how long)

    -- in place of Algorithm 1's report line:
        add (pos, T, copy of nowval) to pending
        for each ob in pending:             -- newest included
            v := CHECK(ob); if v /= undecided: report (ob.pos, v), drop ob
        drop from every tab[j] the rows older than the earliest window still
        awaited by pending (all rows if pending is empty)

    at end of trace:
        for each ob in pending: report CHECK(ob) with every query exact
            -- closes the windows: an unwitnessed F is false, an
            -- unrefuted G true

**Checking an obligation.** The verdict for position `p` is the value of
`root` computed from the values of all subformulas at `p`. For past and
propositional subformulas those values never change after `p` — the
obligation's snapshot `vals` holds them, final. Only the future nodes'
entries are provisional, and their *eventual* answers may not be known
yet. `CHECK` handles this by computing two roots instead of one:

- `root_lo` — each future node contributes only what its table already
  **proves**: its window query, as of now.
- `root_hi` — each future node is additionally credited with the
  **best a future event could still do** for it: for `F`, a witness may
  still arrive while the deadline is ahead; for `U`, only for runs still
  alive in `A`. A node whose answer is *final* — deadline passed, runs
  dead, or trace over — gets no such credit: there `hi = lo`.

Tables only grow, so the true eventual root value lies between the two:
`root_lo  =>  eventual  =>  root_hi`. One wrinkle: for a future node
sitting under a negation, more witnesses make the root *falser*, not
truer — so at such a node `lo` and `hi` trade places (the node's
*polarity*: the parity of negations on its path to the root).

The sandwich decides:

    CHECK(p, time, vals):                 -- time: the anchor for p's windows
        for each future node j:
            lo[j] := the window query over tab[j], anchored at p
            hi[j] := lo[j] if j's answer is final,
                     else lo[j] weakened by the best still possible
            swap lo[j], hi[j] if j lies under an odd number of negations
        root_lo := root evaluated over vals, with entry j := lo[j]
        root_hi := root evaluated over vals, with entry j := hi[j]
        if root_lo is true:          return true
            -- even with no further help, p already holds
        if root_hi is false:         return false
            -- even crediting all possible help, p fails
        if every j's answer final:   return root_lo   -- lo = hi: exact
        return undecided

In the worked trace above: at event 2, position 1 has `root_lo = false`
(no `done` yet) but `root_hi = true` (a run is alive, the deadline
ahead) — undecided. At event 3 the query alone proves it:
`root_lo = true`, resolved two time units *before* the deadline. And at
end of trace position 4 is final with `root_lo = root_hi = false`.

**The combined algorithm** is Algorithm 1 with the two changes in place:

    pre[n] := false;  tab[j] := empty;  pending := {};  pos := 0

    for each event E (with timestamp T):
        pos := pos + 1
        for each node n, bottom-up:
            case n of
              ...                         -- the cases of Algorithm 1
              future (j): ...             -- Change 1
            simplify now[n];  nowval[n] := export(n, now[n])
        pre := now;  preval := nowval
        park, check pending, prune tables -- Change 2 (replacing report)

    at end of trace: force the pending obligations        -- Change 2

The `debug` flag shows all of this live: the formula tree per event, each
node annotated with its current formula, plus the positions still
pending.

This is the same recurrence the original DejaVu runs over BDDs; carrying
formulas instead is what admits data theories (arithmetic, strings, enums,
bit-vectors) and symbolic parameters. Per-step formulas are kept small by
simplification (`strong`/`weak` select the level) and, on long traces, by
garbage collection of dead value-terms (`gc`). The known limitation:
growth from genuinely-live data (many distinct values live at once) is
not bounded — `gc` reclaims dead terms, not a large live set.

The rest of this document is the design, feature by feature:

- [Timed (metric) operators](#timed-metric-operators)
- [Bounded future operators](#bounded-future-operators)
- [Parametric monitoring](#parametric-monitoring)
- [Rules, sequences, states, actions](#recursive-rules-and-state-variables)
- [Python functions inside formulas](#python-functions-inside-formulas)

---

# Timed (metric) operators

How DejaVuMT implements `S[a,b]`, `S[a,*]`, `Z[..]`, `P[..]`, `H[..]` and
the sugar `[<=n] [<n] [>=n] [>n]`. Companion to the "Metric Operators"
section of the paper; this is the implementation view.

## Timed traces

A timed trace attaches to every event an absolute, non-decreasing integer
timestamp `T` — in the CSV log, the last column of each line (DejaVu's
format): `open,a,17` is `open(a)` at time 17. Timed operators speak about the
**age** of a past event: current timestamp minus the timestamp of the
witnessing occurrence.

    phi S[a,b] psi   --  psi held between a and b time units ago,
                         and phi has held at every step since.

To recall: semantically `P[a,b] phi = true S[a,b] phi` and `H[a,b] phi = !P[a,b]!phi`.
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

Although the semantics of Z, P and H are *defined* by these rewrites, the engine does not
compile them that way: every surface operator (S, Z, P, H — timed and untimed)
gets its
own node interpreting its own (provably equal) recurrence, so the debug tree
mirrors the specification one-to-one, with no encoding artifacts (no
constant-`true` child under P, no `¬P¬` chain for H). The P and H
recurrences are given at the end of the next section.

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

A record is written once and never touched again — there is no per-step
aging. It is the *query* that moves: the window constraint
`a <= T - t <= b` is re-evaluated against each new timestamp `T`. The
state is kept small through the two bounds, which behave differently:

- **Upper bound `b`.** A record's age only grows, so once it exceeds `b`
  the record can never satisfy the window again. Such records are
  deleted: the state never holds more than the last `b` time units of
  history.
- **Lower bound `a`.** A record with age below `a` does not satisfy the
  window *yet* — but it will, once enough time has passed. Deleting it
  would therefore be wrong: the lower bound only filters the query's
  answer, and the record stays in the state.
- **No upper bound (`[a,*]`).** Now no record ever becomes useless, so
  nothing may be deleted. But once a record's age reaches `a`, it
  satisfies the window from then on, forever — *when* it happened has
  stopped mattering. The engine therefore forgets the timestamp: all such
  records are merged into a single formula without `t`, which from then
  on evolves like ordinary untimed state.

This defines the `bound` operation of the overview's loop (`_bound_state`
in `engine.py`). It acts per node: only a subformula headed by a timed
past operator carries a window, and the node supplies its own window
`[a,b]` and its own time variable `t` (`T` is the current timestamp);
every other node passes through unchanged. (Future-operator tables are
kept small by their own rule — see the pruning paragraph under bounded
future operators.)

    bound(S)  =  S with every record of age > b deleted   -- past, window [a,b]
                 (its stamp t = c rewritten to false)

    bound(S)  =     QElim( Exists t . S and T - t >= a )  -- past, window [a,*]
                 or ( S and T - t < a )
                 -- matured records merged, t eliminated;
                 -- young records kept, stamps untouched

    bound(S)  =  S            -- every other node: untimed, future (tables
                              -- pruned by their own rule), or a parametric
                              -- bound (nothing may be dropped)

The other past operators run recurrences of the same shape. `P[a,b] phi`
drops the since-recurrence's phi-conjunct — once a witness is on record,
nothing more is required of the steps after it:

    S  <-  (B[phi] and t = T)  or  pre[S].

`H[a,b] phi` is P in disguise (`H = !P[a,b]!phi`): its table records the
positions where `phi` **failed**, stamped like any witness. The initial
state `false` then means "no failure on record", which is exactly H's
vacuous truth at the start of the trace; and the node exports the
*negation* of the window query over this failure table — "no failure in
the window". One consequence for `debug` output: an H node's state line
describes `!phi` (the recorded failures), while its value line describes
`phi`.

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
close(b)@12`. Actual `debug` output (the unlabeled annotation on each node is
its stored slot; where the exported value differs — timed and H nodes — it
follows, labeled `value:`):

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
on it ("holds iff n >= 7") — see
[parametric monitoring](#parametric-monitoring). For the past
operators the verdicts come for free (a past verdict is known at its own
position); the price is state: with `n` symbolic neither the expiry pruning
nor the `[a,*]` saturation of this section applies — every record matters
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

---

# Bounded future operators

How DejaVuMT implements `X`, `U[a,b]`, `F[a,b]`, `G[a,b]` and their unbounded
forms. Companion to the "Bounded Future Operators" section of the paper; this
is the implementation view.

## The difficulty, and the notebook

A property with a future operator cannot in general be judged at its own
position: whether `F[<=5] ack(x)` holds at position *i* depends on events not
yet read. So the monitor does what a person would: it writes the outstanding
requirement in a **notebook** — "awaiting an `ack(a)` between times 3 and 8" —
and returns to it as events arrive, crossing it off when it is fulfilled, or
when its deadline passes unfulfilled.

Two consequences for the interface:

- **Verdicts carry positions.** `Monitor.step(event, ts)` returns the verdict
  of each property *for this position*, which may be `None` (pending). Every
  verdict determined during that step — for this position or an earlier one —
  is in `Monitor.resolved`, a list of `(position, property, holds)`.
- **The trace must be closed.** `Monitor.end()` forces every remaining
  obligation to a verdict (an unwitnessed `F` becomes false, an unrefuted `G`
  true) and returns them the same way. The CLI and the web UI call it after
  the last event.

## One mechanism: until

Everything is an instance of until. A `U[a,b]` node stores **two** stamped
tables, updated eagerly at every event, both recording observed facts only:

    A  <-  A or (t = T)            # runs reaching this position
    W  <-  W or (psi and A and t' = T)
    A  <-  phi and A               # to reach the next position, phi must hold now

Read them as relations with named columns:

- `A` has columns (data, `t`): a row is a **run** — phi has held from time `t`
  up to now. Deleted, pointwise per data value, when phi fails.
- `W` has columns (data, `t`, `t'`): a row is an **answered run** — the run
  begun at `t` was answered by a psi at `t'`.

Hence the two time columns: a row of `W` is not a witness alone but a witness
*together with the run it answers*, since one psi answers every run reaching
its position. Note the update order: `W` is extended *before* phi is tested,
because phi is required strictly before the witness, not at it.

## Obligations

At each event the tree is evaluated bottom-up as always; a future node exports
its query's value over the table *so far* — a lower bound on the eventual
answer. The root's value is then parked, verbatim, as an obligation
`(position, frozen values)` in the **pending list**. It is checked
immediately: obligations whose future parts turn out not to matter (a false
antecedent) resolve at once.

Implementation note: the paper presents the parked formula as containing an
opaque constant `Q`. The engine instead freezes the whole `nowval` array and
*recomputes* the path from the future nodes to the root at check time
(`_recompute`). The two are equivalent, and recomputation avoids substituting
a data-dependent formula underneath a quantifier.

## Checking: brackets

Each future node's eventual export lies between a lower and an upper bound
(tables only grow; for `G`, whose table records counterexamples, the bounds
are mirrored). Substituting the bounds according to each node's **polarity**
w.r.t. the root brackets the eventual verdict:

- `phi_lo` true  -> the verdict is true, **early** (a witness cannot be revoked);
- `phi_hi` false -> the verdict is false, **early** (e.g. the run is broken);
- every query **exact** -> the brackets coincide: emit the verdict.

A query is exact once its deadline has passed, or — for until — once its
anchors are dead. Polarity is computed on the compiled tree (`_compute_polarity`):
`+1` under an even number of negations, `-1` under an odd number, `0` in both
senses (under `<->`), in which case that obligation simply waits for exactness.
No syntactic restriction on where future operators may occur is needed.

The first check of an obligation, made at the event that creates it, comes out
false and resolves nothing: before the deadline, false means *not yet*.

## Special cases

`F[a,b] phi = true U[a,b] phi`: anchors never die, the anchor column of `W`
becomes redundant, and the node keeps a single table `S` of witness stamps.
`G[a,b] phi = !F[a,b] !phi`: the table records phi's counterexamples and the
node exports the negated query. `X phi` is the degenerate case, stamped by
**position** rather than by time, with window `[1,1]`. Unbounded `F`, `G`, `U`
(no interval) also use positions, so they need no timestamps at all: `F p`
runs on an untimed log, with the end of the trace as the only forcing point.

## Pruning

A table row can serve no obligation once its stamp lies before the earliest
pending window, and no row at all is needed when the pending list is empty —
so the tables are cleared outright then. This is the dual of the past
operators' rule, where the moving window kills records from behind.

## Nesting: placeholders and staged resolution

A future operator below a *stateful* operator (`P (F[<=2] p)`,
`a S (F[<=2] p)`, `@ (F..)`) or inside another future operator's argument
(`F[<=5] (p & F[<=3] q)`) poses a harder problem: the enclosing recurrence
needs the inner node's value *at each position as input*, and that value is
still pending there. Such "deep" nodes export, instead of a lower bound, an
**opaque placeholder**: an uninterpreted predicate `_q..(x..)` applied to the
node's free data variables (a predicate, not a constant, so that quantifiers
above bind through it). The placeholder flows into states and tables like any
subformula; `simplify` cannot touch it.

Resolution is staged, innermost first: once a placeholder's answer is final
(deadline passed or run dead) *and* its node's tables mention no other
unresolved placeholder, its value is computed from the tables and
**substituted, as a function, into everything** — node states, exported
values, future tables, and parked obligations (`backend.substitute_fun`,
capture-safe under binders). Early verdicts still work: unresolved
placeholders in an obligation's formula are bracketed by substituting bound
functions (today's value / ⊤) according to the placeholder node's polarity,
which composes through stateful operators as well (every recurrence is
monotone or antitone in each input — see `OPSIGNS`).

Shallow nodes (only stateless ancestors) keep the direct query mechanism —
the common request-response case pays nothing for any of this.

## Example

`examples/future/`, run with

    python -m dejavumt examples/future/prop.qtl examples/future/log.csv trace

The spec is `Forall x . req(x) -> F[<=5] ack(x)`; the log is

    req,a,3       position 1: pending
    ack,b,4       holds at once (no req)
    ack,a,6       answers position 1 -> holds, early (deadline was 8)
    req,c,10      pending
    other,x,20    deadline 15 has passed -> position 4 VIOLATED, here

`debug` additionally prints, under each tree, the positions still awaiting a
verdict.

---

# Parametric monitoring

An interval bound — upper or lower — of any timed operator, past
(`P/H/S/Z`) or future (`F/G/U`), may be a *symbolic parameter* instead of a
number. (A bound that names a variable a quantifier *binds* is a different
feature — a **data-dependent bound** like `Forall n . a(n) -> F[0,n] b`,
with ordinary Boolean verdicts; see
[variable bounds](#variable-bounds). A parameter is a name
bound by nothing: the monitor's output constrains it.)

    pred req(x: String)
    pred ack(x: String)
    prop r : Forall x . req(x) -> F[<=n] ack(x)

The monitor leaves `n` free and reports, per position, the **constraint on
`n`** under which that position holds, plus a running **feasible region** —
the conjunction of the constraints so far:

    --- r at event 1: req(a) @ 0 holds iff 7 <= n
    --- r at event 3: req(b) @ 10 holds iff 3 <= n

    Parametric verdict for r: holds iff 7 <= n

Instead of checking one deadline, the monitor *synthesizes* the tightest
deadline the trace meets. In the API, verdicts from `Monitor.step`/`end` are
then backend formulas rather than Booleans, and each `FormulaMonitor`
exposes the region as `region`.

## Why it is almost free

The engine is symbolic throughout: timestamps, data values, and window
bounds are all just terms in formulas. A parameter is an Int constant
(`FormulaMonitor.params`) that the engine simply *never eliminates*, so the
usual value query `Exists t . S & T+a <= t <= T+n` eliminates to a formula
over `n`, and the root of the property becomes the verdict constraint. The
tables, queries, and recurrences are untouched; `n` flows through them like
any constant. Only two things change: how verdicts are *decided* (below,
different for past and future), and what can be *pruned*.

## Past operators: immediate verdicts, growing state

A past verdict is fully known at its own position, so the constraint is
emitted immediately — no obligations, no brackets (`step` routes the root
through `_pverdict` instead of the Boolean `_verdict`).

The cost moves to state: a parametric past window can prune nothing. A
record at any age is still inside the window for large enough `n` and
outside it for small `n`, so neither expiry (upper-bound pruning) nor
saturation (the `[a,*]` projection of matured records) applies, and that
node's state grows with the trace (`_bound_state` returns the state as-is).

## Future operators: finality by bracket agreement

A parametric window has no numeric deadline, so `_fexact` never closes it.
Instead the node's bracket in `_check` is

    [ q ,  q | n >= max(a, elapsed) ]

any *future* witness lies at delay >= the time elapsed since the anchor
(timestamps are non-decreasing), so the most it can still contribute is
`n >= elapsed`. The obligation resolves when the two eliminated root
brackets agree **for every parameter value** (one satisfiability check of
their iff). Consequences:

- `F` resolves at the **first witness** — a later one is only slower, hence
  subsumed;
- `G` resolves at the first counterexample;
- `U`'s upper bracket is tightened to `q | (alive & n >= max(a, elapsed))`,
  where `alive` is the run's surviving data values (from the `A` table): a
  future witness also needs `phi` to have held since the anchor, so a
  broken run collapses the brackets and yields `false` for every `n` at
  once (the run-death satisfiability check in `_fexact` fires
  independently of `n`);
- anything still open resolves at end of trace (`false` for every `n` if
  unanswered, collapsing the region).

## Lower bounds: discovered minimum delays

An upper-bound parameter synthesizes the tightest deadline met (`n >= 7`);
a lower-bound parameter is the antitone twin and synthesizes guaranteed
*minimum* ages and delays — thresholds of the form `n <= d`:

    prop t : Forall x . rsp(x) -> P[>=n] req(x)     -- every response's
                                                       request was at least
                                                       n old: holds iff n <= 3

Mechanically the lower bound is the easier direction for the future
operators: `F[n,10]` still has its *concrete* deadline at +10, so the
standard finality machinery applies unchanged — the obligation resolves
when time passes the deadline, with the constraint `n <= (witness delay)`.
`F[n,*]` has no deadline and resolves at end of trace. On the past side,
`P[n,10]` keeps its expiry pruning (expiry depends only on the concrete
upper bound), while `P[>=n]` can neither expire nor saturate and grows like
the parametric-upper case. At most one bound per operator may be symbolic
(`P[m,n]` is rejected); distinct operators may carry distinct parameters.

## The feasible region

Emitted constraints accumulate into `FormulaMonitor.region`, the parameter
values under which every judged position holds. It only shrinks, and it is
kept subsumption-free (two satisfiability checks per emission: skip a
constraint the region already implies, replace the region by a strictly
stronger constraint). An empty region is the parametric analogue of a
violation: no parameter value rescues the trace.

## Well-formedness

Checked at compile time (`collect_params`, plus the deep-node check in
`FormulaMonitor.__init__`):

- a parameter occurs in **exactly one** bound — upper or lower, on any
  timed operator — and an operator carries at most one symbolic bound;
- a parameter name must not also be used as a data variable.

Parametric operators may **nest anywhere**. Past occurrences are known at
their own position; a nested (deep) future occurrence with a symbolic
*upper* bound has no deadline, so its placeholder never resolves early —
it is substituted at end of trace, or sooner when its run dies or when the
obligation brackets (pointwise sound in `n`, refined by the same growth
bound) already agree for every parameter value; `@ (F[<=n] p)` still
resolves at the first witness. A nested symbolic *lower* bound keeps its
concrete deadline and resolves early through the ordinary machinery.
Verdicts are exact in all cases (validated by pointwise instantiation
against concrete-bound runs); only latency is conservative — and
deliberately so: parameter *discovery* is inherently a whole-trace
question, so its natural mode is offline log analysis, where end-of-trace
delivery is the norm rather than a defect.

Several *distinct* parameters are fine; verdicts and the region are then
constraints over all of them.

Still open: two symbolic bounds on one operator, multiple or
mixed-polarity occurrences of one parameter, and *eager* resolution of
nested parametric future operators in general (region-guarded staged
resolution — tracking, per placeholder, the parameter region on which its
answer is already final).

---

# Recursive rules and state variables

Two related features close the running-summary gap declaratively: **rules**
(DejaVu's `where` clause) and their functional sugar, **state variables**.

## Rules

    prop r : Forall x . check(x) -> seen(x)
      where seen(x) := p(x) | (@ seen(x))

A rule `r(x̄) := body` is a recursively defined predicate. Its semantics
follows DejaVu exactly:

- **Per-position extension.** At every position the rule's extension is
  recomputed, as if its facts occurred in the trace at that position.
  Compute `o(4)` at one step and `o(5)` at the next, and `o(4)` is
  forgotten — unless a past operator over `o` remembers it in its own
  state.
- **Recursion only under `@`.** Every rule call inside a rule body (self,
  mutual, any) must sit below the previous-operator; the main formula may
  call rules at the current position. This makes rules pure recurrences
  over the previous position — no fixpoint computation — which is exactly
  the shape of every stateful node in the engine.
- Rule parameters must be exactly the body's free variables; call
  arguments are variables (constants are rejected, as in DejaVu); rule
  bodies are past-time.

Implementation: rule bodies compile as ordinary node subtrees, *before*
the main formula (so current-position calls read an already-computed
value); a rule call's value is the body root's value with parameters
renamed to the call's arguments (a constant substitution). Nodes below an
`@` inside a rule body evaluate in a second pass, so a recursive call
there can read its rule root's first-pass value — its own now-value is
only ever consumed next step, through the `@`'s previous-value slot.

**Rules can count.** As formulas over an SMT backend, rule bodies carry
arithmetic, and recursion over positions is what pure first-order logic
lacks for counting:

    prop c : Forall n . check(n) -> count(n)
      where count(n) := ((! @ true) & n = 1)
                      | (Exists m . (@ count(m)) & n = m + 1)

The extension of `count` is a moving singleton — the engine's state for it
is literally the formula `n = 7`. A running sum in constant space; DejaVu's
equality-only rules cannot do this.

## Sequence patterns compile to rules

PSL-style sequences (`{fail(u); fail(u); ok(u)} |-> alarm(u)`) are pure
sugar over rules.  The item list is a regular expression whose atoms are
past-time formulas; a Glushkov construction linearizes it, and each atom
becomes one generated `@`-guarded rule over the sequence's shared
variables:

    _sq0_k(x̄) := atom_k & ( true                -- if k can start a match
                          | @ _sq0_j(x̄) | ... ) -- for each predecessor j

"A match ends here" is the disjunction of the last atoms' calls (plus
`true` if the sequence matches emptily); `seq |-> phi` is that disjunction
implying phi.  Because rules are automata, repetition is full regular
repetition — `{a; {b; b}[*]; c}` (an even number of b's) exceeds plain
LTL's star-free limit and costs nothing here.  Matching uses search
semantics (a match may start at any position) and ends at the current
position, so sequences are past-anchored: they work under quantifiers and
past operators, items must be past-time, and sequences may not appear
inside rule bodies (the generated current-position calls would violate
the `@`-guardedness discipline).  A generated rule carries ALL the
sequence's variables even where its atom mentions fewer — its extension
is then unconstrained in those variables, which the formula
representation handles directly.

## Python actions: producing data during monitoring

Monitors can *produce* data, not only verdicts (PyContract-inspired).
Two attachment sites, both running deliberately side-effecting Python in
the `python:` block's namespace:

    prop c : true
      where count(n) := ((! @ true) & n = 1)
                      | (Exists m . (@ count(m)) & n = m + 1)
                      do {counts.append(n)}

    prop q : Forall f . Forall d . write(f,d) -> P open(f)
        on violation {incidents.append((pos, f))}

- **`do {expr}` on a rule** fires at every position where the rule's
  extension is non-empty **and changed** from the previous position (one
  equivalence check), with the parameters bound to a satisfying
  assignment — exact for functional rules (the moving singleton), a
  representative for multi-valued ones — plus `pos`.
- **`on violation {expr}` / `on satisfaction {expr}` on a property** fire
  once per emitted verdict, in emission order (delayed verdicts fire at
  emission, end of trace included), with `pos` and the witness values
  bound: falsifying values of a leading Forall-prefix for violations,
  satisfying values of a leading Exists-prefix for satisfactions.

Contract: actions may not feed back into the spec's state except through
declared state variables; exceptions in actions abort monitoring with the
rule/property named.

## State variables

The assignment idiom `x := x + 1 on ...` is the *functional* fragment of a
rule, and gets direct syntax with Python step-expressions:

    state total: Int := {0}
        on write(f, d): {total + len(d)}

    prop bound : total <= 1000000

Semantics (equivalently: the functional rule it corresponds to):

- the value starts as the `{init}` expression (evaluated in the `python:`
  block's namespace);
- on each event, every matching `on` clause updates the value — the
  clause's parameters bind the event's arguments (coerced by the declared
  predicate sorts), all state names are in scope with their *previous*
  values, and multiple matching facts fold left-to-right;
- updates run **before** the properties evaluate the event (the rule
  reading: the body pairs the event with the `@`-previous value);
- in formulas the state reads as a **term** — its current ground value
  injected as a literal per position. Atoms mentioning states are
  recompiled per event; everything else (past operators over them,
  quantifiers around them) behaves as with any other value. A `Bool`
  state doubles as an atom.

Because state values are ground by construction, none of the symbolic
machinery is involved: the monitor holds a Python value, and the property
stays whole — the trace the temporal operators see is untouched, unlike
the two-phase TP-DejaVu/PyDejaVu designs, whose examples (running byte
totals, per-file available space) are expressible this way in-spec.
Non-scalar bookkeeping (dicts, sets) lives in Python helper functions,
with scalar projections exposed as state values.

State variables must be pure in the same sense as spec Python functions:
their update expressions may compute anything, but the *monitor-visible*
value per position is the single source of truth.

---

# Python functions inside formulas

Interpreted symbols with lazy graphs. A spec may define Python functions
and use them *inside* formulas:

    python:
        def size(d: str) -> int:
            return len(d)
        def risky(cmd: str) -> bool:
            return cmd in {"rm", "chmod", "dd"}
    end

    pred write(f: String, d: String)
    prop q : Forall f . Forall d . write(f,d) -> size(d) < 100

There is **no pre-phase**: unlike the two-phase designs of TP-DejaVu
(VMCAI 2024) and PyDejaVu (2025), where an operational stage transforms
events before a declarative monitor ever sees them — hiding part of the
property in code — here the property stays whole, in the formula.

## The mechanism

To the engine a Python function is an **uninterpreted SMT function
symbol** (created with `backend.func`, the same machinery as the
staged-resolution placeholders). As a symbol it composes with everything
the engine does — negation, quantifiers, temporal operators, storage in
states, quantifier elimination treats it as opaque — with no fragment
restriction on where it may appear.

Its **graph is supplied lazily**. During each step's normalization the
backend rewrite `eval_funs`:

1. propagates `var = literal` equalities into their sibling subterms —
   within conjunctions, and across the implication shape:
   `!(d=v & R) | C  ==  !(d=v & R) | C[d:=v]` (valid because the first
   disjunct is true whenever `d != v`); this is what makes event-guarded
   applications ground, since a predicate match contributes exactly the
   equalities `d = "abc"`;
2. replaces every application whose arguments are all literals by the
   result of calling the Python function — **memoized** per monitor, so
   functions must be **pure**.

The folded literal then flows like any other value: into since-states,
future-operator tables, obligations. `Forall`/`Exists` above a grounded
application eliminate as usual, since the function symbol is gone before
the quantifier is processed.

## The boundary, honestly

The solver cannot reason symbolically about arbitrary Python (that would
require the function's full graph, or a solver-side axiomatization). So
every verdict-relevant application must become **ground** at some point of
evaluation — in practice: guard its arguments with an event predicate so
the trace supplies them. If a verdict still depends on an unground
application (`Forall d . size(d) > 0` with no guard), the monitor raises a
clear error instead of guessing.

Declarations: functions must carry full type annotations
(`str/int/float/bool` ↔ `String/Int/Real/Bool`); a `bool` function may be
used directly as an atom; others in term position of relations
(`size(d) < 100`, `double(n + 1) > n`). Imports and helper definitions
inside the block are fine (only functions *defined* in the block become
symbols). Function names must not collide with predicates or macros.

## Relation to aggregations (MonPoly)

MonPoly's aggregation operators (SUM/AVG/MAX/CNT) are the *declarative*
route to computing over data: they stay inside the logic but aggregate
over the satisfying assignments of a subformula — which a finite relation
can enumerate and a symbolic formula-state in general cannot. The design
space is a triangle:

- **pointwise computation** — this feature: pure functions of data
  values, fully general, composes with the symbolic engine;
- **aggregation** — declarative operators, feasible exactly where a
  subformula's assignment set is finitely enumerable; a natural companion
  of future hybrid relational-state work;
- **operational summaries** (TP-DejaVu / PyDejaVu pre-phase) — rejected
  here: hides the property.

Stateful functions (accumulating across calls) are deliberately out:
call order/count during symbolic evaluation is an implementation detail,
and memoization assumes purity. For running summaries, use **state
variables** and **recursive rules** (above) — the declarative route to
counting and sums; MonPoly-style aggregation over satisfying assignments
remains tied to the relational-state work.


# Work the engine avoids

Everything above describes what the monitor computes. Done literally, it is
slow in a way that has little to do with the logic: on a typical log most
events are irrelevant to most properties, yet each still costs a full
bottom-up pass, a satisfiability check, and — for a future property — a new
obligation checked at full cost. The engine therefore skips work whose
result it already knows. None of this changes a verdict; each step below
was checked against the engine without it, verdict by verdict.

## Pure solver calls are cached

Quantifier elimination and simplification are pure functions of their
argument, and Z3 hash-conses terms, so a term's id identifies it exactly.
A monitor asks for the same few terms again and again — an event that
leaves a subformula unchanged re-requests its value — so both are cached,
in a bounded LRU whose entries keep their argument alive (an id cannot be
recycled while cached). On recorded logs, 81% of eliminations and 95% of
simplifications were repeats.

For the same reason the obligation check of a future property caches its
recomputation of the path from the future nodes to the root (`_recompute`):
it runs twice per obligation per event, and on an irrelevant event it reads
the same terms as last time.

## Irrelevant events, once the property has settled

An event is *irrelevant* to a property when it holds none of the
predicates the property mentions. On such an event every atom is false,
and every past operator's update is either idempotent — `P`, `H`, `S` and
the interval all have the shape `now := a ∨ (b ∧ pre)` — or reads the
previous step (`@`, `Z`). So within one or two irrelevant events the whole
tree stops changing. The engine does not reason about this operator by
operator; it observes it: if an irrelevant event left every node's state
and exported value the *same term*, the next irrelevant event will too, and
from then on irrelevant events are skipped, the verdict carried over.

Two things can still change without a relevant event:

- **Time.** A timed node's value changes when a witness ages into or out of
  its window. Its state records each witness as `t = c`, so the earliest
  moment one enters (`c + lo`) or leaves (`c + hi + 1`) the window is read
  off the state, and the property is evaluated again at that deadline. If
  `t` occurs in any other form, or a bound is symbolic, the deadline is
  unknown and the property is evaluated in full.
- **Future obligations.** A property with future operators settles only
  from a *quiet* state: the irrelevant event's own obligation was decided on
  the spot, nothing is pending, no placeholder awaits resolution, and the
  step changed no future table. An obligation checked at its own position
  compares its clock with itself plus a fixed bound, so the next irrelevant
  event reaches the same decision. Anything that differs by position shows
  up as a changed term and prevents settling: an until run is stamped with
  its position, and a nested future operator gets a fresh placeholder per
  position, so `U` and deeply nested `F` never skip.

The skip is deliberately conservative. Only a plain `true` verdict is
carried over — a violation owes a witness and its `on violation` action at
every position — and it is off altogether where "this event holds none of
my predicates" might not mean "this event cannot affect me", or where a
skipped position would owe more than its verdict: state variables (another
property's action can change them on any event), Python functions (which
need not be pure), rule and `on satisfaction` actions, anchored and
parametric properties, weak mode, and the CVC5 backend.

## Empty future tables

A future node keeps a table of the witnesses it has observed, and the event
it awaits is usually rare, so the table is almost always empty: on a
recorded log, 12,369 of 12,377 table queries were on an empty table. A
query over an empty table is false, and an update that observes nothing
leaves the table unchanged; both are now recognised without building the
formula they would have produced.

## Time-limited elimination only where it is needed

`qe2` can diverge on string concatenations and regular expressions, so
quantifier elimination runs under a three-second limit. The limit costs a
fixed 65–185 µs per call to arm its timer, which on specs without strings
was 15–30% of all monitoring time. The backend therefore applies it only
once the spec has built a string term — all such terms are built while the
spec is compiled, before any quantifier is eliminated — and uses plain
`qe2` otherwise.

## The effect

On twelve recorded logs of an F′ temperature-control deployment (329 to
7,396 events each; seven properties covering past, future, timed and
untimed operators), all verdicts identical:

| engine | total time |
|---|---|
| without these steps | 236.7 s |
| with them | 11.5 s |

Per event, a *relevant* event costs what it always did; what changed is
that the other events — 99% of these logs — no longer cost the same.

