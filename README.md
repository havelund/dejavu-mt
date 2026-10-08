# DejaVuMT

Runtime verification for first-order temporal logic: [DejaVu's](https://github.com/havelund/dejavu) QTL extended
with future and timed operators, parametric bounds (symbolic time bounds,
for which the monitor synthesizes the constraints under which the trace
satisfies the property), string matching, sequence patterns, recursive
rules, state variables, and Python functions in formulas.
It is written in Python and represents monitor state as SMT formulas
(over Z3 or CVC5) where DejaVu uses BDDs. DejaVu's BDDs support data,
but essentially only equality comparisons; the SMT representation adds
reasoning in data theories (arithmetic, strings, enums, bit-vectors) and
verdicts that are *constraints* rather than just true/false.

The SMT representation also yields a comparatively simple implementation:
the logic's semantics maps almost directly onto recurrences over formulas,
with the solver doing the heavy lifting, where the BDD solution encodes
data, and in particular time, into bit vectors. The price paid is speed
(see [performance](#performance)): this is a study in expressiveness
rather than efficiency.

The language manual is [doc/language.md](doc/language.md); the design,
per feature, is [doc/engine.md](doc/engine.md).

Contents:
[quick start](#quick-start) ·
[a first example](#a-first-example) ·
[the specification language](#the-specification-language) ·
[command-line reference](#command-line-reference) ·
[web interface](#web-interface) ·
[library API](#library-api) ·
[performance](#performance) ·
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

- **Past operators** `@ S Z P H [_,_)`.
- **Future operators** `X U F G`, freely nested with the past ones; a
  future verdict is reported once known — possibly at a later event, or
  at end of trace.
- **Timed variants** of the temporal operators (`P[<=5]`,
  `busy U[2,7] ack`), checked against timestamped logs.
- **Parametric bounds**: `req(x) -> F[<=n] ack(x)` with `n` symbolic —
  verdicts become constraints on `n`, and the monitor synthesizes the
  tightest deadline the trace meets.
- **Typed quantification** over `String`, `Int`, `Real`, `Bool`,
  bit-vectors, and enumerations.
- **Relations with arithmetic** (`v2 = v1 + 1`).
- **String matching** with capture holes (`m matches "user {u}"`).
- **Sequence patterns** (`{fail(u); fail(u); ok(u)} |-> P vetted(u)`).
- **Recursive rules** (`where seen(x) := p(x) | @ seen(x)`) — reaching
  transitive closure and counting.
- **State variables**, updated per event by Python expressions.
- **Python functions**, callable inside formulas
  (`write(f,d) -> size(d) < 100`).
- **Python actions**, fired on violations, satisfactions, and rule
  matches.
- **Anchored properties**: judged once for the whole trace instead of at
  every position.

The full reference — semantics of every operator, the type system, log
formats, and the grammar — is the language manual,
[doc/language.md](doc/language.md).

## Command-line reference

    python -m dejavumt <spec.qtl> <log> [trace] [debug] [strong|weak] [z3|cvc5] [gc] [json] [timed]

The log is CSV, or JSONL if the extension is `.jsonl`/`.ndjson`/`.json`
(see the [manual](doc/language.md#what-is-being-monitored)). The `timed`
flag marks the log's last CSV column as a timestamp even when the spec
uses no timed operators (automatic when the spec is timed, or when the
filename contains `.timed.` — DejaVu's convention).

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

**Loading.** Each editor pane has a file bar: `open…` browses the repository
tree (`.qtl` specs, `.csv` and `.jsonl` logs — a log pasted or loaded into
the editor is recognized as JSONL when its first line starts with `{`).
Spec and log are picked independently, so directories with
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

For embedding the monitor in a Python program instead of running the CLI —
events can then come from anywhere (a socket, a running system, a test
harness), not just a log file. The CLI and the web UI are both thin loops
over this API.

    from dejavumt import parse_spec, Monitor

    m = Monitor(parse_spec(spec_text))          # or solver="cvc5"
    for ev in events:                           # ev = {"open": [("a","read")]}
        m.step(ev)      # verdict for this position — possibly None (future ops)
        m.resolved      # every (position, property, holds) decided by this step
    m.end()             # closes the future windows; returns the final resolutions

`step(ev)` feeds one event — a dict from predicate name to a list of
argument tuples (several facts, of several predicates, allowed) — and
returns this position's verdict; with future operators the verdict may not
be known yet, hence possibly `None`. `resolved` is the delayed-verdict
channel: after each step it holds every `(position, property, holds)` that
step decided, including *earlier* positions whose deadline just passed.
`end()` must be called after the last event: it closes the open future
windows (an unwitnessed `F` becomes false, an unrefuted `G` true) and
returns those final resolutions.

Per property (`m.formulas`, one `FormulaMonitor` each): `witnesses` maps a
violated position to the falsifying values (`{"f": "b"}`), and for
parametric specs `region` holds the accumulated constraint on the symbolic
bounds — verdicts are then backend formulas rather than booleans.

## Performance

A speed-limit warning: the focus of this project has been the
*expressiveness* of a first-order temporal logic, not efficiency, and every
step that does real work runs through an SMT solver rather than a compiled
data structure. The engine does, however, avoid most of the work a log
presents. A property is evaluated in full only on events that mention one
of its predicates, at the moment a timed operator's window boundary passes,
and while one of its future obligations is outstanding; any other event
costs almost nothing once the property has settled (see *Work the engine
avoids* in [doc/engine.md](doc/engine.md)). Throughput therefore depends on
how many events are relevant to a property, not on how long the log is.

On recorded logs of an F′ temperature-control deployment — seven
properties, past and future, timed and untimed, over logs in which 99% of
the events are telemetry no property mentions — DejaVuMT checks 1,700 to
2,200 events per second, start-up included. A relevant event still costs
tens of microseconds to milliseconds of solver work. Measured before these
optimisations, that put DejaVuMT two to four orders of magnitude behind
MonPoly and the BDD-based DejaVu per event; `experiments/perf_bench.py`
reproduces the comparison. Long logs are a matter of patience, not blowup —
with one exception: properties tracking many distinct data values live at
once grow the monitor's state (`gc` reclaims dead values, not live ones).
Offline analysis of moderate logs remains the natural mode; high-throughput
online monitoring of event-dense traces is not the current target.

## Documentation

- [doc/language.md](doc/language.md) — the language manual: every
  construct, with the grammar at the end.
- [doc/engine.md](doc/engine.md) — how the engine works, overall and per
  feature (timed, future, parametric, rules/sequences/states, Python
  functions).
- [doc/validation.md](doc/validation.md) — the comparisons with DejaVu,
  MonPoly, and the reference evaluator.
