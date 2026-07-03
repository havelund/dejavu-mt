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

    python -m dejavumt <specfile.qtl> <logfile.csv> [trace] [debug] [strong|weak] [z3|cvc5] [gc]

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

### Garbage collection

Over a long trace a subformula's formula can accumulate "dead" value-terms —
terms about a value that dropped out of the live set (e.g. a resource granted
and later revoked) but that the fast per-step simplifier leaves standing. The
`gc` flag periodically (every 50 events) runs a contextual simplifier over the
stored formulas to prune them, the analogue of DejaVu's garbage collection of
dead values:

    python -m dejavumt examples/churn/prop.qtl examples/churn/log.csv gc

It is verdict-preserving. On churn workloads it keeps the representation bounded
(see `experiments/gc_bench.py`: the accumulating formula grows to thousands of
nodes without `gc` and stays at a constant handful with it). It does not help
when the growth is genuinely-live data (many distinct values live at once), which
has no dead terms to reclaim. Currently Z3-only (it uses Z3's `ctx-simplify`).

### Solver backend

The monitor runs on either Z3 (default) or CVC5, selected with the `z3` / `cvc5`
flag:

    python -m dejavumt examples/file/prop.qtl examples/file/log.csv cvc5 trace

Both backends produce identical verdicts (the recurrence engine is
solver-agnostic; only the leaf-level SMT operations differ — see
`dejavumt/backend.py`). Z3 is a required dependency; CVC5 is optional and only
imported when selected:

    .venv/bin/pip install cvc5

Note: `strong` simplification is Z3-only (it uses Z3's `ctx-solver-simplify`,
which has no CVC5 equivalent); it is ignored on the CVC5 backend.

### Combining

`trace` and `debug` can be combined. `debug` behaves exactly as on its own
(the per-event formula trees), and the `trace` table is appended as one
contiguous block at the end:

    python -m dejavumt examples/file/prop.qtl examples/file/log.csv trace debug

## Specification language

The specification language is DejaVu's QTL — a typed first-order *past-time*
linear temporal logic — with optional type annotations on declared parameters.
A specification is a sequence of declarations, macro definitions and properties:

    pred open(f: String, m: String)     // event/predicate declarations
    pred close(f: String)

    pred isOpen(f) = [open(f,m),close(f))          // a macro (abbreviation)

    prop file : Forall f . close(f) -> Exists m . @ [open(f,m),close(f))

### What is being monitored

A **trace** is a finite sequence of **events**, read one at a time. Each event
is a set of ground **facts** — predicate instances such as `open("a","read")`.
An event may contain several facts, including several of the *same* predicate
(e.g. both `p(1)` and `p(2)` at one step). A **property** is a closed formula;
after each event the monitor reports whether the property *holds* or is
*violated* at that point in the trace. In the CSV log format one line is one
fact (`open,a,read`), so each line is a one-fact event.

### Types

Every predicate parameter has a type (sort), defaulting to `String` if the
annotation is omitted; the supported sorts are `String`, `Int`, `Real`, `Bool`.
A variable's type is inferred from how it is used (the predicate positions it
appears in, or numeric constants it is related to). Types are what enable
*theory* reasoning: `<` on `Int`/`Real` is numeric order, on `String` it is
lexicographic, and arithmetic is available on the numeric sorts. This is the
main gain over DejaVu's untyped, equality-only BDD encoding.

### Grammar

    spec        ::= definition*
    definition  ::= declaration | macro | property

    declaration ::= ("pred" | "event" | "preds" | "events") predsig ("," predsig)*
    predsig     ::= name [ "(" [ typedparam ("," typedparam)* ] ")" ]
    typedparam  ::= name [ ":" sort ]
    sort        ::= "String" | "Int" | "Real" | "Bool"

    macro       ::= "pred" name [ "(" [ name ("," name)* ] ")" ] "=" formula
    property    ::= "prop" name ":" formula

    formula     ::= "Exists" name "." formula          // quantifiers bind loosest
                  | "Forall" name "." formula
                  | formula "->" formula | formula "<->" formula
                  | formula "|"  formula
                  | formula "&"  formula
                  | leaf "S" leaf                       // since
                  | leaf
    leaf        ::= "true" | "false"
                  | expr relop expr                     // relation
                  | name [ "(" [ term ("," term)* ] ")" ]   // predicate / macro call
                  | "!" leaf                            // negation
                  | "@" leaf                            // previous
                  | "P" leaf                            // once   (sometime in the past)
                  | "H" leaf                            // historically (always in the past)
                  | "[" formula "," formula ")"         // interval
                  | "(" formula ")"
    relop       ::= "=" | "<" | "<=" | ">" | ">="

    expr        ::= expr "+" product | expr "-" product | product   // arithmetic
    product     ::= product "*" atom | atom
    atom        ::= name | int | float | string | "-" atom | "(" expr ")"
    term        ::= name | int | float | string        // predicate arguments

    // Comments are // to end of line, or /* ... */. Strings use "double quotes".

Precedence, from loosest to tightest binding: quantifiers, then `-> <->`, `|`,
`&`, `S`, then the unary leaf operators. Quantifiers scope over everything to
their right, so `Forall f . close(f) -> phi` means `Forall f . (close(f) -> phi)`.

### The operators

Propositional: `!` (not), `&` (and), `|` (or), `->` (implies), `<->` (iff).

Past-time temporal (all refer only to the past and present):

| operator | meaning |
|---|---|
| `@ phi` | `phi` held at the **previous** step (previous / yesterday) |
| `phi S psi` | `psi` held at some past step and `phi` held at every step **since** |
| `P phi` | `phi` held at some past-or-present step (**once**) |
| `H phi` | `phi` held at **every** past-or-present step; equal to `!P!phi` |
| `[phi, psi)` | `phi` held at some past-or-present step and `psi` has **not** held since (half-open interval) |

Quantifiers `Exists x . phi` and `Forall x . phi` range over the *full*
(possibly infinite) domain of `x`'s type; they translate directly to Z3
quantifiers.

Relations `= < <= > >=` compare two expressions of compatible type. Relation
operands may be arithmetic expressions built with `+ - *` and unary minus, e.g.
`v2 = v1 + 1` or `a * 2 <= b`; the variables involved must be numeric
(`Int`/`Real`), typically via their predicate declarations. Arithmetic is not
allowed inside predicate arguments (those are plain variables or constants).

Macros (`pred name(args) = formula`) are named abbreviations, expanded
syntactically before monitoring.

## Status (slice 1)

Implemented: the untimed first-order fragment — propositional connectives,
`@ S P H` and intervals, quantifiers, macros, and typed relations with
arithmetic (`+ - *`); pluggable Z3/CVC5 backends; and periodic garbage
collection of dead value-terms (`gc`). The engine also accepts events containing
multiple facts (including multiple instances of the same predicate), though the
CSV reader emits one fact per line.

Not yet implemented: timed operators (`S[<=n]`, `P[>n]`, ...), the `Z`
operator, recursive rules (`where ... :=`), and the seen-only lowercase
`exists`/`forall`. Growth from genuinely-live data (many distinct values live at
once) is not yet bounded — `gc` reclaims dead terms but not a large live set,
which would need a more compact set encoding.
