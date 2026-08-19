# Parametric monitoring: symbolic bounds, synthesized constraints

The upper bound of any timed operator — past (`P/H/S/Z`) or future
(`F/G/U`) — may be a *symbolic parameter* instead of a number:

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

- a parameter occurs in **exactly one** bound, and only as an **upper**
  bound, on any timed operator;
- a parameter name must not also be used as a data variable;
- a parametric **future** operator must not be nested under other temporal
  operators: its window never closes, so nested it would need the staged
  resolution of `doc/future.md` to track region-valued exactness (future
  work). Parametric **past** operators may nest anywhere — the recurrences
  carry `n` like any constant.

Several *distinct* parameters are fine; verdicts and the region are then
constraints over all of them.

Still open: symbolic *lower* bounds (antitone: windows shrink as the
parameter grows, so the bracket argument flips), nested parametric future
operators, and multiple or mixed-polarity occurrences of one parameter.
