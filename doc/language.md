# The DejaVuMT specification language

The reference manual. The language extends DejaVu's QTL — a typed
first-order *past-time* linear temporal logic — with future and timed
operators, parametric bounds (symbolic time bounds, for which the monitor
synthesizes the constraints under which the trace satisfies the property),
string matching, sequence patterns, rules, state variables, and Python.

Contents:
[specifications](#specifications) ·
[what is monitored](#what-is-monitored) ·
[types](#types) ·
[operators](#the-operators) ·
[future operators](#future-operators-and-delayed-verdicts) ·
[anchored properties](#anchored-properties) ·
[timed operators](#timed-metric-operators) ·
[string matching](#string-matching) ·
[Python functions](#python-functions-in-specs) ·
[rules](#recursive-rules) ·
[sequences](#sequence-patterns) ·
[state variables](#state-variables) ·
[parametric monitoring](#parametric-monitoring) ·
[grammar](#grammar)

## Specifications

A specification is a sequence of declarations, macro definitions and
properties:

    pred open(f: String, m: String)     // event/predicate declarations
    pred close(f: String)

    def isOpen(f,m) = [open(f,m),close(f))         // a macro (abbreviation)

    prop file : Forall f . close(f) -> Exists m . @ isOpen(f,m)

Macros (`def name(args) = formula`) are named abbreviations, expanded
syntactically before monitoring; for backwards compatibility with DejaVu
the keyword `pred` is also accepted in the macro form. Comments are `//`
to end of line or `/* ... */`.

## What is being monitored

A **trace** is a finite sequence of **events**, read one at a time. Each event
is a set of ground **facts** — predicate instances such as `open("a","read")`.
An event may contain several facts, including several of the *same* predicate
(e.g. both `p(1)` and `p(2)` at one step). A **property** is a closed formula;
after each event the monitor reports whether the property *holds* or is
*violated* at that point in the trace. Two log formats are read, chosen by
file extension:

- **CSV** (default): one line is one fact with positional arguments —
  `open,a,read` — and, for timed specs, the timestamp as the last column.
  Whether the last column is a timestamp is decided by the
  *specification*: it is read as one exactly when the spec uses timed
  operators (unlike DejaVu, which decides from the log's filename).
  A timed log also works with an untimed spec: pass the `timed` CLI flag,
  or name the log `*.timed.*` (DejaVu's convention, also honored here),
  and the timestamp column is consumed without the properties using it.
- **JSONL** (`.jsonl`/`.ndjson`/`.json`): one JSON object per line, fields
  matched **by name** to the predicate's declared parameters (order
  irrelevant, extra fields ignored, missing declared fields an error);
  JSON numbers/booleans flow into typed parameters directly, and for
  timed specs the integer field `"time"` is the timestamp:

      {"name": "open", "f": "data.txt", "m": "w", "time": 3}

## Types

Every predicate parameter has a type (sort), defaulting to `String` if the
annotation is omitted; the supported sorts are `String`, `Int`, `Real`,
`Bool`, the bit-vector sorts `BV8`/`BV16`/`BV32`/`BV64`, and declared
**enumerations**:

    enum Mode = OFF | STANDBY | ACTIVE
    pred set(m: Mode)
    pred fire(m: Mode)

    prop safe    : Forall m . fire(m) -> m = ACTIVE
    prop covered : eof -> Forall m . P set(m)   -- every mode exercised

Quantifiers over an enum range over exactly its constructors — which makes
**coverage properties** like `covered` expressible (over an infinite sort
they are trivially false).

**Bit-vectors** carry an unsigned reading with wraparound `+ - *`, unsigned
`< <= > >=`, hex literals, and the named operations `band bor bxor bnot
shl lshr` (infix `&`/`|` would collide with the connectives):

    pred stat(w: BV16)
    pred frame(c: BV16)

    prop err  : Forall w . stat(w) -> band(w, 0x40) = 0
    prop inc  : Forall c . Forall c0 .
        (frame(c) & @ frame(c0)) -> c = c0 + 1     -- modulo 2^16

A variable's type is inferred from how it is used: the predicate positions it
appears in, numeric constants it is related to; a variable used in
`< <= > >=` with no other type information defaults to `Int` (declare it
`String` explicitly if you want lexicographic comparison). A quantified
variable may also carry an explicit annotation — `Forall m: Mode . ...` —
which is authoritative, like a predicate declaration; useful where inference
has nothing to go on (e.g. a variable used only in variable-variable
equalities). Types are what enable *theory* reasoning: numeric order,
lexicographic order, and arithmetic on the numeric sorts.

**Relations** `= < <= > >=` compare two expressions of compatible type.
Relation operands may be arithmetic expressions built with `+ - *` and unary
minus, e.g. `v2 = v1 + 1` or `a * 2 <= b`; the variables involved must be
numeric (`Int`/`Real`), typically via their predicate declarations.
Arithmetic is not allowed inside predicate arguments (those are plain
variables or constants).

## The operators

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

Past and future operators alike may carry an optional **time bound**
(`P[<=5] open`, `F[<=5] ack`, `busy U[2,7] ack`), described in
[timed operators](#timed-metric-operators) below. Without a bound no
timestamps are needed: unbounded operators work on ordinary untimed logs.

Quantifiers `Exists x . phi` and `Forall x . phi` range over the *full*
(possibly infinite) domain of `x`'s type; they translate directly to SMT
quantifiers.  A quantifier scopes over everything to its right, up to the
parenthesis (or end of formula) that closes the enclosing formula — so
`Forall f . close(f) -> phi` means `Forall f . (close(f) -> phi)`. A quantifier may also appear inside a formula — negated, as in
`! Exists i . phi`, or as an operand, as in `a | Exists m . phi` — and its
scope still runs rightward the same way; parenthesize the quantified
formula itself to limit the scope.

DejaVu's seen-only lowercase `exists`/`forall` are deliberately not
provided. Their universe is derived from the quantified variable's
occurrence positions in the formula, so every meaningful lowercase formula
already contains its own guard as an atom — the uppercase version is the
same formula; the feature's real function in DejaVu is licensing BDD
garbage collection, which has no counterpart here. Name a universe
explicitly with a rule (`resource(r) := ...`) when one is wanted.

## Future operators and delayed verdicts

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

In trace mode, positions whose verdict never resolved show `pending`.

## Anchored properties

By default a property is evaluated at *every* position — one verdict per
position (DejaVu's and MonPoly's convention). For a top-level future formula
that can be noisy: with `prop a : F init`, every position after the last
`init` is a violation. Marking the property **anchored** evaluates it at
position 1 only — the classic `trace |= f` reading, one verdict for the
whole trace:

    prop a anchored : F init

## Timed (metric) operators

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
extensions (one extra linear inequality in the SMT encoding — see
[engine.md](engine.md#timed-metric-operators)).

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
[engine.md](engine.md#timed-metric-operators) for the full story.

A bound may also be a **quantified `Int` variable** — a deadline carried by
the trace, different for every event:

    pred request(x: String, d: Int)
    pred ack(x: String)
    prop own : Forall x . Forall d . request(x,d) -> F[0,d] ack(x)

Verdicts stay Boolean (the quantifier discharges `d`); see
[engine.md](engine.md#variable-bounds). This is distinct from a *symbolic
parameter* bound, where the name is bound by nothing and verdicts become
constraints on it — see [parametric monitoring](#parametric-monitoring).

## String matching

Two relations over `String` terms:

    d contains "AUTOMATIC"          -- substring test
    m matches "user {u}"            -- pattern with holes

`matches` tests a term against a pattern of literal text and **holes**
`{var}`; a hole names a data variable and captures a substring, optionally
constrained by a regular expression: `{n:[0-9]+}`. `{_}` is an anonymous
hole (matches, binds nothing) (subset: literals, `.`,
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
    m has "user {u:[a-z]+}"                 -- sugar for the same (`has`
                                               wraps the pattern in gaps)

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

## Python functions in specs

A spec may define pure Python functions and call them **inside formulas**
— no preprocessing phase, the property stays whole:

    python:
        def size(d: str) -> int:
            return len(d)
        def risky(cmd: str) -> bool:
            return cmd in {"rm", "chmod", "dd"}
    end

    pred write(f: String, d: String)
    pred run(cmd: String)

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
guard) cannot be decided and raises an error. See [engine.md](engine.md#python-functions-inside-formulas) for
how it works and how this differs from the two-phase TP-DejaVu/PyDejaVu
designs and MonPoly's aggregations.

## Recursive rules

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
event) unless a past operator remembers it. See [engine.md](engine.md#recursive-rules-and-state-variables).

**Python actions** turn monitors into data producers: `do {expr}` on a
rule fires when its extension is non-empty and changed (parameters bound
to a satisfying assignment, plus `pos`); `on violation {expr}` and
`on satisfaction {expr}` on a property fire per emitted verdict with
`pos` and the witness values bound (falsifying values of a Forall-prefix,
satisfying values of an Exists-prefix) — all evaluated in the `python:`
block's namespace:

    prop q : Forall f . Forall d . write(f,d) -> P open(f)
        on violation {incidents.append((pos, f))}

## Sequence patterns

PSL-style **sequences** (inspired by IEEE 1850's SEREs), with data
variables shared across the steps:

    prop b : Forall u .
        ({fail(u); fail(u); ok(u); (! sudo(u))[*]; sudo(u)}
            |-> P vetted(u))

`{e1; e2; ...}` matches when the recent trace slices into consecutive
blocks, one per item: a plain item is one position where the formula
holds, `e[*]` any number of positions (each satisfying `e`), `e[+]` at
least one, `e[*n]` exactly `n`; items may themselves be sequences
(`{a; {b; b}[*]; c}` — c after an *even* number of b's, beyond plain
LTL). A match may start anywhere and ends at the current position. As a
formula, `{..}` means "a match ends here"; `seq |-> phi` (suffix
implication) requires `phi` whenever a match ends, with the sequence's
variables bound by the match. Sequences desugar to auto-generated
`@`-guarded rules (a small automaton), so they work under quantifiers and
past operators; items are past-time, and sequences may not appear inside
rule bodies. See [engine.md](engine.md#recursive-rules-and-state-variables).

## State variables

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

## Parametric monitoring

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
[engine.md](engine.md#parametric-monitoring) for how verdicts are decided (immediately for
past operators; by bracket agreement for future ones) and the memory
trade-offs.

## Grammar

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

    macro       ::= ("def" | "pred") name [ "(" [ name ("," name)* ] ")" ] "=" formula
    property    ::= "prop" name [ "anchored" ] ":" formula
                    [ ("on" "violation" pyexpr) | ("on" "satisfaction" pyexpr) ]
                    [ "where" rule ("," rule)* ]
    rule        ::= name [ "(" [ name ("," name)* ] ")" ] ":=" formula
                    [ "do" pyexpr ]

    formula     ::= "Exists" name [":" sort] "." formula   // quantifiers bind loosest
                  | "Forall" name [":" sort] "." formula
                  | seq "|->" formula                      // suffix implication
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

    match       ::= term ("matches" | "has") (string | regex)  // {var} holes, {_} anonymous

    seq         ::= "{" seqitem (";" seqitem)* "}"     // also usable as a formula
    seqitem     ::= (formula | seq) [ "[*]" | "[+]" | "[*" int "]" ]

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
