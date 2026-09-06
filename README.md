# DejaVuMT

Runtime verification for first-order temporal logic: DejaVu's QTL extended
with future and timed operators, parametric (symbolic) time bounds, recursive
rules, sequence patterns, state variables, and Python functions in formulas.
It is written in Python and represents monitor state as SMT formulas
(over Z3 or CVC5) where DejaVu uses BDDs. DejaVu's BDDs support data,
but essentially only equality comparisons; the SMT representation adds
reasoning in data theories (arithmetic, strings, enums, bit-vectors) and
verdicts that are *constraints* rather than just true/false.

Contents:
[quick start](#quick-start) ·
[a first example](#a-first-example) ·
[the specification language](#the-specification-language) ·
[command-line reference](#command-line-reference) ·
[web interface](#web-interface) ·
[library API](#library-api) ·
[validation](#validation) ·
[status](#status) ·
[documentation](#documentation)

## Quick start

    python3 -m venv .venv
    .venv/bin/pip install -e .          # installs z3-solver and lark into .venv
    source .venv/bin/activate           # once per shell

    python -m dejavumt <spec.qtl> <log.csv> [flags]

Example:

    python -m dejavumt examples/file/prop.qtl examples/file/log.csv

For convenience, `./run <example-dir>` runs the spec and log in
`examples/<example-dir>` (with `debug trace strong` by default; pass flags to
override), e.g. `./run file` or `./run demo trace`.

## A first example

`examples/file/prop.qtl` — a file may only be closed if it is open:

    pred close(f: String)
    pred open(f: String, m: String)

    prop file : Forall f . close(f) -> Exists m . @ [open(f,m),close(f))

against the log `examples/file/log.csv` (one fact per line):

    open,a,read
    close,a
    close,b
    ...

The monitor reports each violating event, with the falsifying values of the
quantified variables (a **witness**, extracted from a solver model):

    *** Violation of file at event 3: close(b)  [f=b]

    Processed 6 events, 1 violation(s).

## The specification language

The language extends DejaVu's QTL — a typed first-order past-time linear
temporal logic — into a full temporal logic. In brief:

- **Past operators** `@ S Z P H [_,_)` and **future operators** `X U F G`,
  freely nested; a future verdict is reported once known — possibly at a
  later event, or at end of trace.
- **Timed variants** of all of them (`P[<=5]`, `busy U[2,7] ack`), checked
  against timestamped logs.
- **Typed data**: quantifiers over `String`, `Int`, `Real`, `Bool`,
  bit-vectors and enumerations; relations with arithmetic
  (`v2 = v1 + 1`); string matching with capture holes
  (`m matches "user {u}"`).
- **Parametric bounds**: `req(x) -> F[<=n] ack(x)` with `n` symbolic —
  verdicts become constraints on `n`, and the monitor synthesizes the
  tightest deadline the trace meets.
- **Rules, sequences, states**: recursive rules
  (`where seen(x) := p(x) | @ seen(x)` — they can count and sum),
  PSL-style sequence patterns
  (`{fail(u); fail(u); ok(u)} |-> P vetted(u)`), and state variables
  updated by Python expressions.
- **Python**: pure functions callable inside formulas
  (`write(f,d) -> size(d) < 100`), and actions fired on rule matches,
  violations and satisfactions.
- **Anchored properties**: judged once for the whole trace instead of at
  every position.

The full reference — semantics of every operator, the type system, log
formats, and the grammar — is the language manual,
[doc/language.md](doc/language.md).

## Command-line reference

    python -m dejavumt <spec.qtl> <log> [trace] [debug] [strong|weak] [z3|cvc5] [gc] [json]

The log is CSV, or JSONL if the extension is `.jsonl`/`.ndjson`/`.json`
(see the [manual](doc/language.md#what-is-being-monitored)).

### trace

Prints one line per event with its per-property verdict. The table is
printed once the trace has been read (future verdicts may resolve late);
never-resolved positions show `pending`, and an anchored property's
unjudged positions show `-`.

### debug

Prints what the engine is doing: at startup, the declarations and each
formula as an indented AST tree; per event, the same tree with every node
annotated by its current SMT formula (pretty-printed in `∀ ∃ ∧ ∨ ¬ →`
notation, colored green/red/yellow for true/false/other), plus the
positions still awaiting a verdict. `trace` and `debug` combine — the
trace table is appended at the end.

### strong

By default each node's formula is normalized with Z3's fast (syntactic)
`simplify`, which can leave logically-trivial residue (e.g. an unsatisfiable
conjunction not reduced to `false`). `strong` additionally runs the
solver-backed `ctx-solver-simplify`, which collapses such contradictions and
subsumed terms. It is opt-in because it is much slower (a solver call per
node per event, ~20x on the access benchmark) — intended for clean `debug`
output on small traces, not for performance runs. Z3-only.

### weak

The opposite extreme: *no* simplification or quantifier elimination as
formulas move up the tree, showing the raw output of the recurrences (e.g.
`(a S b)` unfolding to `(false | (true & (false | ...)))`). A debugging aid
for seeing the formula semantics literally; the verdict stays correct, but
formulas grow quickly, so only practical on very short traces. Overrides
`strong`.

### gc

Over a long trace a subformula's formula can accumulate "dead" value-terms —
terms about a value that dropped out of the live set (e.g. a resource
granted and later revoked) but that the fast per-step simplifier leaves
standing. `gc` periodically (every 50 events) runs a contextual simplifier
over the stored formulas to prune them — the analogue of DejaVu's garbage
collection of dead values. Verdict-preserving; on churn workloads it keeps
the representation bounded (see `experiments/gc_bench.py`). It does not help
when the growth is genuinely-live data, which has no dead terms to reclaim.
Z3-only.

### json

Writes a machine-readable record of the run to `<logfile>.results.json`:
per property its text, anchored flag, the verdict at every position
(`true`/`false`/`null`, or a constraint string for parametric properties),
the violations with their witnesses, and the parametric region; plus the
final state-variable values.

### z3 | cvc5

Selects the solver backend (default `z3`). Both produce identical verdicts
(the recurrence engine is solver-agnostic; only the leaf-level SMT
operations differ — see `dejavumt/backend.py`). CVC5 is an optional
dependency (`pip install cvc5`); `strong` and `gc` are ignored on it.

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

## Library API

    from dejavumt import parse_spec, Monitor

    m = Monitor(parse_spec(spec_text))          # or solver="cvc5"
    for ev in events:                           # ev = {"open": [("a","read")]}
        m.step(ev)      # verdict for this position — possibly None (future ops)
        m.resolved      # every (position, property, holds) decided by this step
    m.end()             # closes the future windows; returns the final resolutions

Witnesses of violations are in each `FormulaMonitor`'s `witnesses`
(position → `{var: value}`); parametric properties expose `region`, and
their verdicts are backend formulas instead of booleans.

## Validation

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
transitive-closure rule pairs with a small `--max-events`. DejaVu decides
that a log is timed from its **filename** (it must contain `.timed.`); the
harness mirrors this convention.

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

Implemented — the logic: the first-order fragment (connectives,
`@ S Z P H` and intervals, full-domain typed quantifiers with optional
sort annotations, macros), typed relations with arithmetic, the timed
operators with the `[<=n] [<n] [>=n] [>n]` sugar, the bounded future
operators `X`/`U[..]`/`F[..]`/`G[..]` (nestable anywhere — under
negation, below past operators, inside each other), parametric bounds on
every timed operator (verdicts become constraints on `n`), data-dependent
bounds (`Forall n . a(n) -> F[0,n] b`), string matching (`contains`,
`matches`/`has` with capture holes), enumeration sorts, bit-vectors,
recursive rules, sequence patterns (`{e1; e2[*]; e3} |-> phi`), state
variables, Python functions inside formulas, Python actions
(`do`/`on violation`/`on satisfaction`), and anchored properties.

Implemented — the tooling: pluggable Z3/CVC5 backends; violation (and
satisfaction) witnesses from solver models; CSV and JSONL logs; JSON
results recording (`json` flag); the web UI; periodic garbage collection
of dead value-terms (`gc`). The engine accepts events containing multiple
facts (including several of one predicate), though the log readers emit
one fact per line.

Deliberately not implemented: DejaVu's seen-only lowercase
`exists`/`forall`. Its universe is derived from the quantified variable's
occurrence positions in the formula, so every meaningful lowercase formula
already contains its own guard as an atom — the uppercase version is the
same formula. The feature adds neither expressiveness nor, in practice,
brevity; its real function in DejaVu is the `bounded` annotation licensing
BDD garbage collection, which has no counterpart here. Name a universe
explicitly with a rule (`resource(r) := ...`) when one is wanted.
Likewise not adopted, with rationales in `TODO.md`: SALT-style scope and
abort operators (each reduces to a one-operator guard already present).

Known limitation: growth from genuinely-live data (many distinct values
live at once) is not yet bounded — `gc` reclaims dead terms but not a
large live set. The design notes for the planned fix live in `TODO.md`
(Optimization notes).

## Documentation

- [doc/language.md](doc/language.md) — the language manual: every
  construct, with the grammar at the end.
- [doc/timed.md](doc/timed.md) — how the timed operators are encoded.
- [doc/future.md](doc/future.md) — future operators and delayed verdicts.
- [doc/parametric.md](doc/parametric.md) — parametric monitoring: how
  constraint verdicts are decided.
- [doc/rules.md](doc/rules.md) — rules, sequence patterns, state
  variables, actions.
- [doc/pyfun.md](doc/pyfun.md) — Python functions in formulas.
- `DEJAVU.md` — the repair of the original DejaVu used for validation.
- `TODO.md` — roadmap, decisions, optimization notes.

How the engine works, in one paragraph: each subformula node holds an SMT
formula over its free variables in two copies — `pre` (previous position)
and `now`. On every event the `now` formulas are recomputed bottom-up
following the temporal-logic semantics, and the closed top formula is
checked for satisfiability to yield the verdict. Quantifiers translate
directly to SMT quantifiers over each variable's declared sort. The `debug`
flag shows all of this live.
