# DejaVuMT

Runtime verification for first-order past-time LTL (DejaVu's QTL), using an SMT
solver (Z3) instead of BDDs.

Each subformula node holds a Z3 **formula** over its free variables, in two
copies — `pre` (previous position) and `now` (current position). On every event
the `now` formulas are recomputed bottom-up following the Boolean-formula
semantics of past-time LTL, and the closed top formula is checked for
satisfiability to yield the verdict. Quantifiers translate directly to Z3
quantifiers over each variable's declared sort, which is what lets the logic
reason about data theories (arithmetic, strings, orders) beyond DejaVu's
equality-only BDD encoding.

## Install

    python3 -m venv .venv
    .venv/bin/pip install -e .

This installs the dependencies (`z3-solver`, `lark`) into the `.venv`
virtual environment, not into your system Python.

## Run

Activate the virtual environment once per shell (otherwise the dependencies are
not found: `ModuleNotFoundError: No module named 'lark'`):

    source .venv/bin/activate

then run:

    python -m dejavumt <specfile.qtl> <logfile.csv> [trace] [debug] [strong|weak]

Example:

    python -m dejavumt examples/file/prop.qtl examples/file/log.csv

For convenience, `./run <example-dir>` runs the spec and log in
`examples/<example-dir>` (with `debug trace strong` by default; pass flags to
override), e.g. `./run file` or `./run demo trace`.

### Trace mode

Adding `trace` prints one line per event with its per-property verdict:

    python -m dejavumt examples/demo/prop.qtl examples/demo/log.csv trace

### Debug mode

Adding `debug` prints what the engine is doing:

    python -m dejavumt examples/file/prop.qtl examples/file/log.csv debug

It shows (A) at startup, the event/predicate declarations and the formula as an
indented AST tree; and (B) for each observed event, the event followed by the
same tree with every node annotated by its current Z3 `now` formula (pretty-
printed in `∀ ∃ ∧ ∨ ¬ →` notation, colored green/red/yellow for
true/false/other). This makes the `pre`/`now` recurrence directly visible: e.g.
an `@` node shows the previous step's value of its child, and a `Since`/interval
node shows its accumulated formula.

### Strong simplification

By default each node's formula is normalized with Z3's fast (syntactic)
`simplify`, which can leave logically-trivial residue (e.g. an unsatisfiable
conjunction not reduced to `false`). Adding `strong` additionally runs the
solver-backed `ctx-solver-simplify`, which collapses such contradictions and
subsumed terms:

    python -m dejavumt examples/file/prop.qtl examples/file/log.csv debug strong

It is opt-in because it is much slower (a solver call per node per event, ~20x
on the access benchmark), so it is intended for clean output on small traces,
not for performance runs. It does not help genuine accumulation (e.g. many
distinct values), which needs garbage collection instead.

### Weak (no simplification)

The opposite extreme, `weak`, does *no* simplification or quantifier elimination
as formulas move up the tree, showing the raw output of the recurrences (e.g.
`(a S b)` unfolding to `(false | (true & (false | ...)))`). It is a debugging aid
for seeing the Boolean-formula semantics literally; the verdict stays correct
(quantifiers are eliminated only on a throwaway copy of the root, so it does not
hang). Because nothing is collapsed, the formulas grow quickly, so `weak` is only
practical on very short traces. It overrides `strong`.

    python -m dejavumt examples/file/prop.qtl examples/file/log.csv debug weak

### Combining

`trace` and `debug` can be combined. `debug` behaves exactly as on its own
(the per-event formula trees), and the `trace` table is appended as one
contiguous block at the end:

    python -m dejavumt examples/file/prop.qtl examples/file/log.csv trace debug

## Specification language

DejaVu's QTL, with optional type annotations on declared parameters
(default `String`):

    pred open(f: String, m: String)
    pred bid(i: String, a: Int)

    pred isOpen(f) = [open(f,m),close(f))          // macro

    prop file : Forall f . close(f) -> Exists m . @ [open(f,m),close(f))

Operators: `-> <-> | & !`, `@` (previous), `S` (since), `P` (once),
`H` (historically), `[phi,psi)` (interval), `Exists`/`Forall`, and relations
`= < <= > >=` over typed terms.

## Status (slice 1)

Implemented: the untimed first-order fragment — propositional connectives,
`@ S P H` and intervals, quantifiers, macros, and typed relations.

Not yet implemented: timed operators (`S[<=n]`, `P[>n]`, ...), the `Z`
operator, recursive rules (`where ... :=`), the seen-only lowercase
`exists`/`forall`, and multiple predicate instances per event. Growth of the
`now` formulas is currently controlled only by Z3 `simplify`; this is the thing
to measure next.
