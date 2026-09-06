# How the engine works

Each subformula node holds an SMT formula over its free variables in two
copies — `pre` (previous position) and `now`. On every event the `now`
formulas are recomputed bottom-up following the temporal-logic semantics
(e.g. `p S q` becomes `q ∨ (p ∧ pre(p S q))`), and the closed top formula
is checked for satisfiability to yield the verdict; then `now` becomes
`pre` and the next event is read. Quantifiers translate directly to SMT
quantifiers over each variable's declared sort. The `debug` flag shows all
of this live: the formula tree per event, each node annotated with its
current formula.

This is the same recurrence the original DejaVu runs over BDDs; carrying
formulas instead is what admits data theories (arithmetic, strings, enums,
bit-vectors) and symbolic parameters. Per-step formulas are kept small by
simplification (`strong`/`weak` select the level) and, on long traces, by
garbage collection of dead value-terms (`gc`).

The refinements per feature have their own notes: timed operators stamp a
time variable and project it out ([timed.md](timed.md)); future operators
park obligations and emit verdicts once known ([future.md](future.md));
parametric bounds are constants never eliminated, so verdicts become
constraints ([parametric.md](parametric.md)); rules evaluate as recurrences
over the previous position ([rules.md](rules.md)); Python functions are
uninterpreted symbols given their values once arguments become ground
([pyfun.md](pyfun.md)).
