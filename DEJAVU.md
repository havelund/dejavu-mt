# Fixing the quantifier-scope bug in DejaVu

Plan for repairing the original (BDD-based) DejaVu, at
https://github.com/havelund/dejavu. Drafted from the findings of the
DejaVuMT differential validation (see `experiments/ab_report.md` and
`experiments/dejavu-parser-fix/`).

## STATUS: DONE (2026-07-11) — branch `fix-quantifier-scope` in ~/Desktop/development/dejavu

The fix has been applied and verified in the fresh clone
(`~/Desktop/development/dejavu`, commit `e60b351`, not yet pushed):

- Parser fix applied exactly as planned (`ltlLeaf` -> `ltl` + PackratParsers).
- Also fixed `Settings.PROJECT_DIR`, which was hardcoded to a nonexistent
  machine path (`/Users/khavelun/...`) — without this the JUnit suite cannot
  run at all.
- **JUnit suite** (run with scalac 2.12 + JUnitCore, no sbt): 245 of 250 test
  methods pass. The fix introduces **zero** new failures and **repairs 44**
  methods that had been failing on master since 2021: Test3 fifo (2), Test20
  (4), Test18_gc (38). Surprise: the recorded expectations in Test3/Test20
  were never downgraded to leaf semantics — they encode the intended
  wide-scope verdicts, so they pass unchanged (plan step "update stale
  expectations" turned out unnecessary). The 5 remaining failures (Test10: 1,
  Test15: 2, Test18_gc: 2) fail identically on unfixed master — pre-existing,
  unrelated to the fix, still to be triaged separately.
- **Differential harness vs DejaVuMT** (`ab_validate.py --dejavu-cp ...`):
  DEJAVU_ERROR dropped 101 -> 0; MATCH rose 82 -> 170 (at 1000-event prefixes),
  and all 13 slower pairs also MATCH at 300-event prefixes. After one further
  DejaVuMT fix (below): **zero mismatches — every comparable pair agrees.**
- Bonus finding (bug in DejaVuMT, fixed there): DejaVu compares order
  relations *numerically* (`toInt`); DejaVuMT had been defaulting untyped
  order-related variables to String (lexicographic). DejaVuMT now defaults
  such variables to Int.

## ALL UPSTREAM ITEMS DONE (2026-07-11) — branch pushed

Branch `fix-quantifier-scope` pushed to github.com/havelund/dejavu
(commits `e60b351` parser+settings fix, `ffffac2` jar+test+notes).
PR can be opened at: https://github.com/havelund/dejavu/pull/new/fix-quantifier-scope

- Fat jar rebuilt from fixed sources, now bundling the Scala 2.12 runtime
  (2.11 no longer builds on modern JDKs); verified fully self-contained
  end-to-end (codegen -> scalac -> run -> correct verdicts).
- `test58_parsing` added: parses every .qtl in the repo under a 2 s/spec
  budget — the regression test that would have caught the 2021 blowup.
- `RELEASE-NOTES.md` added: behavioral change, migration note (add parens to
  keep tight binding), parser memoization, jar/Scala-version note.
- The 5 "pre-existing failures" were triaged and FIXED: all were
  order-sensitivity of garbage-collection notices ("n -- value") in
  `checkResults` — their order follows hash-map iteration and varies across
  JVM/Scala versions. Violations are still compared in order; GC notices now
  order-insensitively (TestCase.scala).
- **Final suite status: 58 classes / 251 methods, all passing** (Scala 2.12,
  JDK 11). Master had 49 failing before the branch.

**MERGED TO MASTER and pushed (2026-07-11):** master is now `ffffac2`
(fast-forward). The 2021 quantifier-scope bug is fixed in the public repo.
Optionally remaining (Klaus): tag a release; delete the
`fix-quantifier-scope` branch if no longer wanted.

## The problem

Commit `55fdb2c` (2021-07-28, "sped up parser") restricted the bodies of the
capital quantifiers to a single leaf:

```scala
"Forall" ~ name ~ "." ~ ltlLeaf ^^ { // TODO : change back to ltl
"Exists" ~ name ~ "." ~ ltlLeaf ^^ { // TODO : change back to ltl
```

This was a deliberate workaround: with full `ltl` bodies, the backtracking
combinator parser re-parses the quantifier body once per operator alternative,
compounding per nesting level — measured today, five specs of the distribution
(the locks/dataraces/deadlocks family and test27) take more than 10 seconds to
parse, one 9.6 s. The same commit hand-parenthesized ~20 test specs so they
would still parse under the tight binding, which is why the regression suite
kept passing and the workaround went unnoticed for four years.

Consequences in the current distribution (found by running all 333 (spec, log)
pairs through both DejaVu and DejaVuMT):

1. **~100 spec/log pairs are rejected** by DejaVu's own well-formedness check
   with "variable occurs free" — including documented examples such as
   `out/examples/auction/prop1.qtl` — because in
   `Forall u . login(u) -> logout(u)` the tight binding leaves `logout(u)`
   outside the quantifier.
2. **Two accepted specs are silently vacuous** (`test3_fmcad_fifo/spec.qtl`,
   `test20/spec4.qtl`): the implication ends up outside the quantifier, the
   antecedent `forall x . p(x)` is almost always false, and the monitor
   reports no violations where real ones exist (fifo out-of-order exits;
   a telemetry error inside a command's execution window). For a runtime
   verification tool this silent-false-negative form is the serious one.

## The fix

Restore wide scope AND remove the reason for the workaround, by making the
parser memoizing (Packrat). Three mechanical edits to
`src/main/scala/dejavu/Parser.scala`:

1. `class Parser extends JavaTokenParsers with PackratParsers`
2. Parser productions `def X: Parser[T] = ...` become
   `lazy val X: PackratParser[T] = ...` (and the small token defs
   `le lt ge gt eq oper` become `lazy val`). Bodies unchanged.
3. In the two quantifier productions: `ltlLeaf` -> `ltl` (delete the TODO).

`PackratParsers` is part of scala-parser-combinators (already a dependency);
memoization caches each (production, position) result so backtracking never
re-parses the same text.

A ready-made transformed file, verified against the shipped jar, is at
`experiments/dejavu-parser-fix/ParserPackrat.scala` (class renamed
`ParserPackrat` there; rename back to `Parser` when applying).

Measured results (all 115 specs of the distribution, Scala 2.12):

| parser              | scope | corpus parse times |
|---------------------|-------|--------------------|
| shipped (`ltlLeaf`) | wrong | fast; rejects ~100 own pairs, 2 specs vacuous |
| revert only (`ltl`) | right | 5 specs > 10 s (exponential backtracking) |
| revert + Packrat    | right | all parse; avg 39 ms, max 55 ms |

Verified: the Packrat parser produces identical ASTs to the plain wide parser,
and previously rejected specs are well-formed under wide scope.

## Plan

1. **Apply the parser fix** (edits above) on a branch.
2. **Re-run the JUnit suite.** Most tests pass unchanged (the 2021
   hand-parenthesized specs parse identically — explicit parens are explicit).
   Two recorded expectations encode the vacuous reading and must be updated to
   the intended semantics:
   - `test3_fmcad_fifo`: violations become {6, 14, 16, 17, 21}
     (was {6, 16, 21}).
   - `test20/spec4` on log2: violation at event 10 (was none).
3. **Rebuild the fat jar** (`out/artifacts/dejavu_jar/dejavu.jar`) so the
   distribution matches the source.
4. **Independent verification:** re-run DejaVuMT's differential harness
   (`experiments/ab_validate.py`) against the rebuilt jar. Expected: the
   101 DEJAVU_ERROR pairs and 2 MISMATCH pairs all convert to MATCH.
5. **Guard against regression:** add a test that parses every `.qtl` in the
   repository under a time bound (driver: `experiments/dejavu-parser-fix/
   Bench.scala`). This is the test that would have caught the blowup in 2021.
6. **Release notes / version bump.** This is a behavioral change:
   - specs previously rejected with "variable occurs free" now parse;
   - quantifiers now scope to the end of the formula (the documented,
     intended reading); any spec that relied on the old tight binding
     changes meaning — add parentheses to keep the old reading.

## Housekeeping while in there

- `out/examples/README` documents examples the shipped jar could not run;
  after the fix this inconsistency disappears (verify auction examples run).
- After the upstream fix, DejaVuMT's README/paper can drop the "DejaVu rejects
  its own specs" caveat and report plain agreement on the suite.

## Artifacts

- `experiments/dejavu-parser-fix/ParserPackrat.scala` — the fixed parser
- `experiments/dejavu-parser-fix/ParserWide.scala` — scope fix only (for A/B)
- `experiments/dejavu-parser-fix/Bench.scala`, `Cmp.scala` — timing / AST-equality drivers
- `experiments/dejavu-parser-fix/corpus_times.txt` — per-spec timings
- `experiments/ab_validate.py`, `experiments/ab_report.md` — the differential
  harness and the run that surfaced all of this
