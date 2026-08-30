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

## Web interface

A local browser UI (spec and log editors, an examples browser, the trace
table, and — its main attraction — the per-event annotated formula trees of
debug mode, rendered with colors):

    .venv/bin/pip install flask      # one-time; or: pip install -e ".[web]"
    ./start_web.sh                   # http://localhost:5001  (or: ./start_web.sh 8080)

The script restarts any running instance (log at `/tmp/dejavumt_web.log`);
`python -m dejavumt.web [port]` runs the server in the foreground instead.
The `help` button in the page header shows this in short form.

**Loading.** Each editor pane has a file bar: `open…` browses the repository
tree (any `.qtl`/`.csv` under it, including the DejaVu distribution in
`requirements/`). Spec and log are picked independently, so directories with
several specs and logs work — with shortcuts for the common cases: clicking
a folder that holds exactly one spec and one log (and no subfolders) loads
both at once; picking a spec auto-loads the only log in its folder (and vice
versa); and the browser reopens in the directory you last used.

**Running and saving.** Run verifies what is *in the editors* — files are
untouched until you press `save`, which writes the pane to the (editable)
path in its file bar; change the path first to save a copy. Choose solver
and modes and Run: events with violations are marked and their formula trees
shown (click an event row to toggle its trees; expand/collapse-all in the
summary line), each node annotated with its stored formula and, where it
differs (timed and `H` nodes), its exported value.

The server binds to `127.0.0.1` only, serves only files under the
repository root, and caps runs at 5000 events / 60 s.

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
*violated* at that point in the trace. Two log formats are read, chosen by
file extension:

- **CSV** (default): one line is one fact with positional arguments —
  `open,a,read` — and, for timed specs, the timestamp as the last column.
- **JSONL** (`.jsonl`/`.ndjson`/`.json`): one JSON object per line, fields
  matched **by name** to the predicate's declared parameters (order
  irrelevant, extra fields ignored, missing declared fields an error);
  JSON numbers/booleans flow into typed parameters directly, and for
  timed specs the integer field `"time"` is the timestamp:

      {"name": "open", "f": "data.txt", "m": "w", "time": 3}

### Types

Every predicate parameter has a type (sort), defaulting to `String` if the
annotation is omitted; the supported sorts are `String`, `Int`, `Real`,
`Bool`, the bit-vector sorts `BV8`/`BV16`/`BV32`/`BV64`, and declared
**enumerations**:

    enum Mode = OFF | STANDBY | ACTIVE
    pred set(m: Mode)

    prop safe    : Forall m . fire(m) -> m = ACTIVE
    prop covered : eof -> Forall m . P set(m)   -- every mode exercised

Constructor names are literals in formulas, and log values are validated
against them (a misspelled `ACTVE` in the log is rejected at read time).
Quantifiers over an enum range over exactly its constructors — which makes
**coverage properties** like `covered` expressible (over an infinite sort
they are trivially false).

**Bit-vectors** carry an unsigned reading with wraparound `+ - *`, unsigned
`< <= > >=`, hex literals, and the named operations `band bor bxor bnot
shl lshr` (infix `&`/`|` would collide with the connectives):

    pred stat(w: BV16)
    prop err  : Forall w . stat(w) -> band(w, 0x40) = 0
    prop inc  : Forall c . Forall c0 .
        (frame(c) & @ frame(c0)) -> c = c0 + 1     -- modulo 2^16
A variable's type is inferred from how it is used: the predicate positions it
appears in, numeric constants it is related to, and — matching DejaVu, which
compares order relations numerically — a variable used in `< <= > >=` with no
other type information defaults to `Int` (declare it `String` explicitly if you
want lexicographic comparison). A quantified variable may also carry an
explicit annotation — `Forall m: Mode . ...` — which is authoritative, like
a predicate declaration; useful where inference has nothing to go on (e.g.
a variable used only in variable-variable equalities). Types are what enable *theory* reasoning:
numeric order, lexicographic order, and arithmetic on the numeric sorts. This
is the main gain over DejaVu's untyped, equality-only BDD encoding.

### Grammar

    spec        ::= definition*
    definition  ::= declaration | macro | property | pythonblock | statedef

    pythonblock ::= "python:" ... "end"        // Python functions for formulas
    enumdef     ::= "enum" name "=" name ("|" name)*
    statedef    ::= "state" name ":" sort ":=" pyexpr
                    ("on" name "(" [ name ("," name)* ] ")" ":" pyexpr)*
    pyexpr      ::= "{" python-expression "}"

    declaration ::= ("pred" | "event" | "preds" | "events") predsig ("," predsig)*
    predsig     ::= name [ "(" [ typedparam ("," typedparam)* ] ")" ]
    typedparam  ::= name [ ":" sort ]
    sort        ::= "String" | "Int" | "Real" | "Bool"
                  | "BV8" | "BV16" | "BV32" | "BV64" | enum-name

    macro       ::= "pred" name [ "(" [ name ("," name)* ] ")" ] "=" formula
    property    ::= "prop" name [ "anchored" ] ":" formula
                    [ ("on" "violation" pyexpr) | ("on" "satisfaction" pyexpr) ]
                    [ "where" rule ("," rule)* ]
    rule        ::= name [ "(" [ name ("," name)* ] ")" ] ":=" formula
                    [ "do" pyexpr ]

    formula     ::= "Exists" name [":" sort] "." formula   // quantifiers bind loosest
                  | "Forall" name [":" sort] "." formula
                  | formula "->" formula | formula "<->" formula
                  | formula "|"  formula
                  | formula "&"  formula
                  | leaf "S" [timebound] leaf           // since (optionally timed)
                  | leaf "Z" [timebound] leaf           // zince (optionally timed)
                  | leaf "U" [timebound] leaf           // until  (future)
                  | leaf
    leaf        ::= "true" | "false"
                  | expr relop expr                     // relation
                  | name [ "(" [ term ("," term)* ] ")" ]   // predicate / macro call
                  | "!" leaf                            // negation
                  | "@" leaf                            // previous
                  | "P" [timebound] leaf                // once   (sometime in the past)
                  | "H" [timebound] leaf                // historically (always in the past)
                  | "X" leaf                            // next   (future)
                  | "F" [timebound] leaf                // eventually (future)
                  | "G" [timebound] leaf                // always (future)
                  | "[" formula "," formula ")"         // interval
                  | "(" formula ")"
    relop       ::= "=" | "<" | "<=" | ">" | ">=" | "contains"

    match       ::= term "matches" string      // pattern with {var} holes

    timebound   ::= "[" bound "," (bound | "*") "]"     // between a and b time units
                  | "[" ("<=" | "<") int "]" | "[" ("<=") name "]"   // sugar
                  | "[" (">=" | ">") int "]" | "[" (">=") name "]"
    bound       ::= int | name        // a name = symbolic parameter, or a
                                      // quantified Int variable (data bound)

    expr        ::= expr "+" product | expr "-" product | product   // arithmetic
    product     ::= product "*" atom | atom
    atom        ::= name | int | float | string | "-" atom | "(" expr ")"
                  | name "(" [ expr ("," expr)* ] ")"   // python function call
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
| `phi Z psi` | `psi` held at some step **strictly** in the past and `phi` held at every step since, through now (**zince**); equal to `phi & @(phi S psi)` |
| `P phi` | `phi` held at some past-or-present step (**once**) |
| `H phi` | `phi` held at **every** past-or-present step; equal to `!P!phi` |
| `[phi, psi)` | `phi` held at some past-or-present step and `psi` has **not** held since (half-open interval) |

Future (they refer to events not yet read, so their verdicts may arrive late —
see below):

| operator | meaning |
|---|---|
| `X phi` | `phi` holds at the **next** step (future dual of `@`) |
| `phi U psi` | `psi` holds at some present-or-future step and `phi` holds at every step until then (**until**) |
| `F phi` | `phi` holds at some present-or-future step (**eventually**); `= true U phi` |
| `G phi` | `phi` holds at **every** present-or-future step (**always**); `= !F!phi` |

`U`, `F` and `G` take the same optional time bound as the past operators
(`F[<=5] ack`, `busy U[2,7] ack`, `G[0,60] !alarm`). Unbounded `F`, `G`, `U`
and `X` need no timestamps and work on ordinary untimed logs.

Quantifiers `Exists x . phi` and `Forall x . phi` range over the *full*
(possibly infinite) domain of `x`'s type; they translate directly to Z3
quantifiers.  A quantifier scopes over everything to its right, and may also
appear nested in operand position (`! Exists i . phi`, `a | Exists m . phi`),
again scoping to the end of the enclosing formula; parenthesize to limit the
scope.

### Future operators and delayed verdicts

A property with a future operator cannot in general be judged at its own
position — whether `F[<=5] ack(x)` holds at event *i* depends on events not
yet read. The monitor therefore parks the requirement and returns to it as
events arrive, so **a position's verdict may be reported at a later event**,
or at the end of the trace, which closes every window (an unwitnessed `F`
becomes false, an unrefuted `G` true). Bounded intervals bound the delay.

    prop resp : Forall x . req(x) -> F[<=5] ack(x)

    req,a,3       position 1: pending
    ack,b,4       holds at once (no req)
    ack,a,6       answers position 1 -> holds, reported here (deadline was 8)
    req,c,10      pending
    other,x,20    deadline 15 has passed -> position 4 VIOLATED, reported here

**Violations come with witnesses.** When a `Forall`-led property fails,
the falsifying values of the quantified variables are extracted from a
solver model and shown with the violation — automatically, for every
property, no message templates needed:

    *** Violation of q at event 3: write(b,boom)  [f=b, d=boom]

(In the API: `FormulaMonitor.witnesses` maps positions to `{var: value}`.)

The `trace` table is therefore printed once the trace has been read, with
every position's verdict filled in (`pending` if it never resolved), and
`debug` lists under each tree the positions still awaiting a verdict. In the
library API, `Monitor.step()` returns the verdict *for this position* —
possibly `None` — while `Monitor.resolved` holds every `(position, property,
holds)` determined by that step, and `Monitor.end()` must be called after the
last event. See `doc/future.md` for the design.

**Evaluation mode.** By default a property is evaluated at *every* position
(one verdict per position — DejaVu's and MonPoly's implicit-G mode; MonPoly
conceptually monitors `□ ∀x̄. φ`). For a top-level future formula that can
be noisy: with `prop a : F init`, every position after the last `init` is a
violation. Marking the property **anchored** evaluates it at position 1
only — the classic `trace |= f` reading, one verdict for the whole trace:

    prop a anchored : F init

Anchored properties are also cheaper (a single parked obligation), and they
combine with parametric bounds (`prop a anchored : F[<=n] init` yields one
constraint on `n`).

### Timed (metric) operators

`S`, `P` and `H` accept a **time bound**, constraining how long ago the
witnessing event happened.  The primitive form is an interval over the event
*age* (current timestamp minus the witness's timestamp): `phi S[a,b] psi`
means "`psi` held between `a` and `b` time units ago, and `phi` at every step
since".  `[a,*]` means "at least `a` time units ago" (no upper bound), and the
comparison forms are abbreviations:

| written | means | reading |
|---|---|---|
| `S[<=n]` | `S[0,n]` | at most `n` time units ago |
| `S[<n]`  | `S[0,n-1]` | less than `n` time units ago |
| `S[>=n]` | `S[n,*]` | at least `n` time units ago |
| `S[>n]`  | `S[n+1,*]` | more than `n` time units ago |

and likewise for `P` and `H` (`P[<=n] phi = true S[<=n] phi`;
`H[a,b] phi = !P[a,b]!phi`; `Z[a,b]`'s witness is read at the previous
step).  DejaVu provides exactly the `[<=n]` and `[>n]` forms of `S`/`P`/`H`
and `Z[<=n]`; the general interval — and the untimed `Z` — are DejaVuMT
extensions (one extra linear
inequality in the SMT encoding — see `doc/timed.md`).

A specification using timed operators is monitored against a **timed log**:
the last column of every CSV line is the event's absolute, non-decreasing
integer timestamp (DejaVu's timed format), e.g. `open,a,17` is `open(a)` at
time 17.  Example:

    pred open(f: String)
    pred close(f: String)
    prop timely : Forall f . close(f) -> P[<=5] open(f)

(see `examples/timed/`).  How it works, in one sentence: a timed node stores
its usual formula extended with one integer time variable `t` stamped with
the witnessing timestamps (`t = 17`), and its exported value is the
quantifier-eliminated projection `Exists t . state & a <= T - t <= b` — see
`doc/timed.md` for the full story.

A bound may also be a **quantified `Int` variable** — a deadline carried by
the trace, different for every event:

    pred request(x: String, d: Int)
    pred ack(x: String)
    prop own : Forall x . Forall d . request(x,d) -> F[0,d] ack(x)

Verdicts stay Boolean (the quantifier discharges `d`); see `doc/timed.md`
("Variable bounds"). This is distinct from a *symbolic parameter* bound,
where the name is bound by nothing and verdicts become constraints on it —
see below.

Relations `= < <= > >=` compare two expressions of compatible type. Relation
operands may be arithmetic expressions built with `+ - *` and unary minus, e.g.
`v2 = v1 + 1` or `a * 2 <= b`; the variables involved must be numeric
(`Int`/`Real`), typically via their predicate declarations. Arithmetic is not
allowed inside predicate arguments (those are plain variables or constants).

### String matching

Two relations over `String` terms:

    d contains "AUTOMATIC"          -- substring test
    m matches "user {u}"            -- pattern with holes

`matches` tests a term against a pattern of literal text and **holes**
`{var}`; a hole names a data variable and captures a substring, optionally
constrained by a regular expression: `{n:[0-9]+}` (subset: literals, `.`,
classes, `* + ?`, `|`, grouping). A capture is a *constraint*, not an
extraction — the pattern means `m = "user " ++ u` — so the hole variable is
an ordinary quantified variable and flows anywhere data flows, e.g.

    prop resp : Forall m . Forall u .
        login(m) & m matches "user {u}" -> F[<=5] logout(u)

Patterns come in two flavours. **Quoted** patterns are literal text with
holes plus `...` **gaps** (match anything, bind nothing) and `{:RE}`
(anonymous constrained gap):

    m matches "...user {u:[a-z]+}..."       -- unanchored capture, no
                                               pre/post variables needed

**Slashed** patterns are a full regex with embedded holes:

    m matches /[a-z ]*user {u:[a-z]+}( .*)?/

Unconstrained gaps at the pattern's ends compile to the native
quantifier-free string atoms (`contains`/`prefixof`/`suffixof`); internal or
constrained gaps use existentially-quantified slack, the shape where string
quantifier elimination may need the bounded fallback.

If a pattern decomposes ambiguously (`"{a}-{c}"` against `"x-y-z"`), **all
decompositions count** (declarative matching, not leftmost-greedy).
Matching log values is as cheap as equality (see
`experiments/string_bench.py`); quantifier elimination over string
constraints can diverge, in which case the engine falls back to leaving the
quantifier in place (a bounded `qe2` attempt) and deciding via the final
satisfiability check.

### Python functions in specs

A spec may define pure Python functions and call them **inside formulas**
— no preprocessing phase, the property stays whole:

    python:
        def size(d: str) -> int:
            return len(d)
        def risky(cmd: str) -> bool:
            return cmd in {"rm", "chmod", "dd"}
    end

    pred write(f: String, d: String)
    prop q : Forall f . Forall d . write(f,d) -> size(d) < 100
    prop r : Forall cmd . run(cmd) -> ! risky(cmd)

Functions need full type annotations (`str/int/float/bool` ↔
`String/Int/Real/Bool`); a `bool` function can be used directly as an
atom, others inside relations (`size(d) < 100`, also with arithmetic
arguments). Imports and helpers inside the block are fine. Functions must
be **pure** — results are cached.

To the engine a function is an SMT symbol whose value is computed by
Python **once its arguments become ground** — which the event that binds
them makes happen. That is also the honest boundary: an application whose
arguments never become ground (`Forall d . size(d) > 0` with no event
guard) cannot be decided and raises an error. See `doc/pyfun.md` for how
it works and how this differs from the two-phase TP-DejaVu/PyDejaVu
designs and MonPoly's aggregations.

### Recursive rules

A property may define **rules** (DejaVu's `where` clause) — recursively
defined predicates whose extension is recomputed at every position, as if
their facts occurred in the trace:

    prop r : Forall x . check(x) -> seen(x)
      where seen(x) := p(x) | (@ seen(x))

Any rule call *inside a rule body* must sit below `@` (recursion is a pure
recurrence over the previous position — no fixpoints); the main formula
may call rules at the current position. Mutual recursion is fine. Rule
bodies are past-time (arithmetic, strings, metric operators all allowed) —
so with arithmetic, rules can count and sum:

    prop c : Forall n . check(n) -> count(n)
      where count(n) := ((! @ true) & n = 1)
                      | (Exists m . (@ count(m)) & n = m + 1)

A rule's extension at each position is forgotten at the next (like an
event) unless a past operator remembers it. See `doc/rules.md`.

**Python actions** turn monitors into data producers: `do {expr}` on a
rule fires when its extension is non-empty and changed (parameters bound
to a satisfying assignment, plus `pos`); `on violation {expr}` and
`on satisfaction {expr}` on a property fire per emitted verdict with
`pos` and the witness values bound (falsifying values of a Forall-prefix,
satisfying values of an Exists-prefix) — all evaluated in the `python:`
block's namespace:

    prop q : Forall f . Forall d . write(f,d) -> P open(f)
        on violation {incidents.append((pos, f))}

### State variables

The functional special case of a rule gets direct, extended-state-machine
syntax: a **state variable** is a ground Python value, updated per matching
event by a braced Python expression (previous state values and the event's
arguments in scope; the `python:` block's helpers usable), and read in
formulas as a term:

    state total: Int := {0}
        on write(f, d): {total + len(d)}

    pred write(f: String, d: String)
    prop bound : total <= 1000000

Updates run *before* the properties see the event. A `Bool` state is
usable directly as an atom (`fire -> armed`); any state under temporal
operators behaves as its per-position literal (`P (total = 4)`).
Non-scalar bookkeeping (dicts, sets) lives in Python helpers, with scalar
projections exposed as states. This covers TP-DejaVu/PyDejaVu-style
running summaries without a preprocessing phase — the update law is in the
spec, and the trace the temporal operators see is untouched.

### Parametric monitoring

An interval bound — upper or lower — of any timed operator, past
(`P/H/S/Z`) or future (`F/G/U`), may be a **symbolic parameter** instead of
a number:

    pred req(x: String)
    pred ack(x: String)
    prop r : Forall x . req(x) -> F[<=n] ack(x)

The monitor leaves `n` free (an ordinary Int constant it simply never
eliminates) and reports, per position, the **constraint on `n`** under which
that position holds, plus a running **feasible region** — the conjunction of
the constraints so far:

    --- r at event 1: req(a) @ 0 holds iff 7 <= n
    --- r at event 3: req(b) @ 10 holds iff 3 <= n

    Parametric verdict for r: holds iff 7 <= n

So instead of checking one deadline, the monitor *synthesizes* the tightest
deadline the trace meets. The past form (`rsp(x) -> P[<=n] req(x)`) works the
same way and is even simpler: a past verdict is fully known at its own
position, so each constraint is emitted immediately. Future verdicts resolve
at the **first witness** (for `F`; a later witness is only slower) or the
first counterexample (for `G`), not at a deadline — with a symbolic bound
there is none; unanswered positions resolve at end of trace (`false` for
every `n`, collapsing the region). For `U` the same holds with one twist: a
future witness also needs its run alive (`p` holding since the anchor), so a
broken run yields `false` for every `n` as soon as it breaks.

The trade: a parametric *past* window can prune nothing — a record at any age
is still in the window for large enough `n` and outside it for small `n` — so
that node's state grows with the trace (like `P[a,*]` without the saturation
rescue). Parametric `F`/`G` obligations, by contrast, die at their first
witness/counterexample as usual.

Well-formedness (checked at compile time): a parameter may occur in **exactly
one** bound, and an operator carries at most one symbolic bound. Parametric
operators may **nest anywhere** — a nested `F[<=n]` has no deadline, so its
verdicts may wait until end of trace (they come earlier when a witness or a
broken run already decides them for every `n`). Several *distinct* parameters
are fine, and each verdict/region is then a constraint over all of them. In
the API, `Monitor.step`/`end` verdicts are then backend formulas (instead of
booleans) and each `FormulaMonitor` exposes `region`. See
`doc/parametric.md` for how verdicts are decided (immediately for past
operators; by bracket agreement for future ones) and the memory trade-offs.

Macros (`pred name(args) = formula`) are named abbreviations, expanded
syntactically before monitoring.

## Validation against the DejaVu suite

`experiments/ab_validate.py` runs every (spec, log) pair shipped with the
DejaVu distribution (333 pairs) through both the original BDD-based DejaVu
(the repaired build — see `DEJAVU.md`) and DejaVuMT, and diffs the verdicts
(sets of violating event numbers) on identical prefix-capped inputs. Results
(`experiments/ab_report.md`), after fixing the quantifier-scope bug in DejaVu
and the bugs listed below in DejaVuMT:

- **275 comparable pairs, 275 identical verdicts, 0 mismatches** — the 206
  rule-free pairs (193 at 1000-event prefixes, the 13 slowest
  quantifier-heavy pairs at 300), plus the **69 rule pairs** (states,
  taskspawning, formalisation benchmarks, sttt_rules; 55 at 1000-event
  prefixes, the transitive-closure taskspawning specs at 150, where the
  per-event relational join stays tractable — one such pair times out at
  1000 events: a performance boundary, not a disagreement). Includes every
  comparable **timed** pair, covering all metric operator forms, with
  DejaVu's recorded JUnit expectations as independent ground truth.
- 68 pairs: outside DejaVuMT's current fragment — 66 lowercase seen-only
  quantifiers (the last DejaVu-parity gap) and one empty spec file — plus
  the intentionally ill-formed wellformedness-test specs.

Note for reruns: pass `--dejavu-cp` pointing at the repaired DejaVu build
(the shipped jar still carries the 2021 quantifier-scope bug), and cap the
transitive-closure rule pairs with a small `--max-events`.

The **future fragment** has no DejaVu counterpart to compare against; it is
validated differentially against a brute-force reference instead
(`experiments/fuzz_reference.py`): a ~100-line transcription of the
assignment semantics, evaluated over the whole finite trace, diffed against
the monitor on random formulas and random timed traces (duplicated
timestamps included). A fixed-seed slice runs in the test suite.

**MonPoly comparison** (`experiments/monpoly.py`, `experiments/monpoly_ab.py`;
MonPoly built at `~/Desktop/development/monpoly`, opam switch `monpoly`):
random formulas of the shared fragment (metric past *and* bounded future)
through both tools — 893 compared, 0 verdict mismatches on MonPoly's
evaluation frontier. Fragment experiment: MonPoly's own `-check` rejects 80%
of random first-order formulas of the shared syntax (negation with free
variables, unbounded future intervals, OR variable mismatches, unbound order
relations, SINCE/UNTIL containment); DejaVuMT monitors all of them.

Performance comparisons (reference evaluator / MonPoly / DejaVu / DejaVuMT)
live in the paper; `experiments/perf_bench.py` reproduces them.

Notes for reproducing timed comparisons: DejaVu decides that a log is timed
from its **filename** (it must contain `.timed.`); the harness mirrors this
convention, and pairs a timed spec only with timed logs.

Over its runs the harness surfaced (and we fixed) five DejaVuMT bugs:
predicate matching is now arity-sensitive like DejaVu's (a 0-ary `close` is
not triggered by `close,data`); undeclared predicates coerce log values to
each argument's inferred sort (so `Forall x . a(x) -> x < 5` works untyped);
untyped variables in order relations default to `Int` (DejaVu compares
numerically); the lexer accepts vertical-tab whitespace (present in DejaVu's
distributed specs); and quantifiers may occur nested in operand position
(`! Exists i . phi`, `a | Exists m . phi`) with wide scope, as in DejaVu's
parser.

## Status

Implemented: the first-order fragment — propositional connectives,
`@ S Z P H` and intervals, quantifiers (top-level and nested), macros, typed
relations with arithmetic (`+ - *`), the timed operators
`S[a,b]`/`S[a,*]`/`Z[..]`/`P[..]`/`H[..]` with the `[<=n] [<n] [>=n] [>n]`
sugar, the bounded future operators `X`/`U[..]`/`F[..]`/`G[..]`,
parametric bounds on every timed operator (`F[<=n]` with `n` symbolic —
verdicts become constraints on `n`), data-dependent bounds
(`Forall n . a(n) -> F[0,n] b`), string matching (`contains`, `matches`
with capture holes), Python functions inside formulas (the `python:`
block), recursive rules (`where r(x) := ...`), state variables
(`state x: Int := {0} on ...`), anchored properties, enumeration sorts,
and bit-vectors;
pluggable Z3/CVC5 backends; and periodic garbage collection of dead
value-terms (`gc`). The engine also accepts events containing multiple facts
(including multiple instances of the same predicate), though the CSV reader
emits one fact per line.

Deliberately not implemented: DejaVu's seen-only lowercase
`exists`/`forall`. Its universe is derived from the quantified variable's
occurrence positions in the formula, so every meaningful lowercase formula
already contains its own guard as an atom — the uppercase version is the
same formula. The feature adds neither expressiveness nor, in practice,
brevity; its real function in DejaVu is the `bounded` annotation licensing
BDD garbage collection, which has no counterpart here. Name a universe
explicitly with a rule (`resource(r) := ...`) when one is wanted. Future operators may occur anywhere — under
negation, below past-time operators (`P (F[<=2] p)`), and nested inside each
other (`F[<=5] (p & F[<=3] q)`). Growth from
genuinely-live data (many distinct values live at once) is not yet bounded —
`gc` reclaims dead terms but not a large live set, which would need a more
compact set encoding.
