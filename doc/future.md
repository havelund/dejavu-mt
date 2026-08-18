# Bounded future operators: design and implementation

How DejaVuMT implements `X`, `U[a,b]`, `F[a,b]`, `G[a,b]` and their unbounded
forms. Companion to the "Bounded Future Operators" section of the paper; this
note is the implementation view.

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
