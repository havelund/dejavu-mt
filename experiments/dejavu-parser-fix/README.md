# Fixing DejaVu's quantifier scope without the 2021 parser blowup

Commit 55fdb2c (2021-07-28, "sped up parser") restricted `Exists`/`Forall`
bodies to `ltlLeaf` as a performance workaround (TODO in Parser.scala says
"change back to ltl"). Consequence today: the shipped jar rejects ~100 of the
distribution's own spec/log pairs ("variable occurs free") and silently makes
some accepted specs vacuous.

Reverting to `ltl` alone reintroduces the 2021 problem — measured here:
5 specs (locks/dataraces/deadlocks family, test27) exceed 10 s to parse due to
exponential backtracking (see corpus_times.txt).

The fix that keeps both: **wide scope + PackratParsers** (memoization).

- `ParserWide.scala`  — Parser.scala with only `ltlLeaf` -> `ltl` (slow on 5 specs)
- `ParserPackrat.scala` — additionally `with PackratParsers` and parser
  productions as `lazy val X: PackratParser[T]` (mechanical transform)

Measured on all 115 specs in the DejaVu distribution (Scala 2.12, shipped jar):

| parser                | result |
|---|---|
| leaf (shipped)        | fast, but wrong scope; rejects ~100 own pairs |
| wide (revert only)    | 5 specs time out (>10 s), one at 9.6 s |
| wide + Packrat        | all 115 parse; avg 39 ms, max 55 ms |

Verified: Packrat and plain-wide produce identical ASTs; previously rejected
specs (e.g. examples/auction/prop1.qtl) are well-formed under wide scope.

Upstream recipe: apply the ParserPackrat transform to Parser.scala, re-run
DejaVu's JUnit suite, then re-run ../ab_validate.py against the rebuilt jar —
the 101 DEJAVU_ERROR pairs and 2 MISMATCH pairs should convert to MATCH.

Bench.scala / Cmp.scala are the measurement drivers (compile against
dejavu.jar; see ab_validate.py for the toolchain env).
