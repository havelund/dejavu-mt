# Validation against DejaVu, MonPoly, and a reference evaluator

## The DejaVu suite

`experiments/ab_validate.py` runs every (spec, log) pair shipped with the
DejaVu distribution (333 pairs) through both the original BDD-based DejaVu
(the repaired build — see `DEJAVU.md` in the repository root) and DejaVuMT,
and diffs the verdicts (sets of violating event numbers) on identical
prefix-capped inputs. Results (`experiments/ab_report.md`), after fixing
the quantifier-scope bug in DejaVu and the bugs listed below in DejaVuMT:

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

Over its runs the harness surfaced (and we fixed) five DejaVuMT bugs:
predicate matching is now arity-sensitive like DejaVu's (a 0-ary `close` is
not triggered by `close,data`); undeclared predicates coerce log values to
each argument's inferred sort (so `Forall x . a(x) -> x < 5` works untyped);
untyped variables in order relations default to `Int` (DejaVu compares
numerically); the lexer accepts vertical-tab whitespace (present in DejaVu's
distributed specs); and quantifiers may occur nested in operand position
(`! Exists i . phi`, `a | Exists m . phi`) with wide scope, as in DejaVu's
parser.

## The future fragment: a brute-force reference

The future fragment has no DejaVu counterpart to compare against; it is
validated differentially against a brute-force reference instead
(`experiments/fuzz_reference.py`): a ~100-line transcription of the
assignment semantics, evaluated over the whole finite trace, diffed against
the monitor on random formulas and random timed traces (duplicated
timestamps included). A fixed-seed slice runs in the test suite.

## MonPoly

`experiments/monpoly.py`, `experiments/monpoly_ab.py` (MonPoly built at
`~/Desktop/development/monpoly`, opam switch `monpoly`): random formulas of
the shared fragment (metric past *and* bounded future) through both tools —
893 compared, 0 verdict mismatches on MonPoly's evaluation frontier.
Fragment experiment: MonPoly's own `-check` rejects 80% of random
first-order formulas of the shared syntax (negation with free variables,
unbounded future intervals, OR variable mismatches, unbound order
relations, SINCE/UNTIL containment); DejaVuMT monitors all of them.

## Performance

Performance comparisons (reference evaluator / MonPoly / DejaVu / DejaVuMT)
live in the paper; `experiments/perf_bench.py` reproduces them.

The paper's figures predate the optimisations described under *Work the
engine avoids* in [engine.md](engine.md), which make events a property does
not mention nearly free; they still describe the cost of a relevant event.
Each of those optimisations was checked against the engine before it, with
verdicts compared at every event: on 100 to 300 random traces covering the
past, future and timed operators (most events irrelevant to most
properties, to exercise the skipping), and on the test suite; all of them
together also on twelve recorded logs of an F′ deployment. No verdict
differed.
