# A/B validation: DejaVu vs DejaVuMT

solver: z3; max events/log: 150; pairs: 3; wall time: 3s

## Summary

- MATCH: 3

## Pairs

| spec | log | events | dejavu viol | mt viol | status |
|---|---|---|---|---|---|
| src/test/scala/tests/test51_sttt_rules/spec.qtl | src/test/scala/tests/test51_sttt_rules/log1.csv | 5 | 1 | 1 | MATCH |
| src/test/scala/tests/test51_sttt_rules/spec.qtl | src/test/scala/tests/test51_sttt_rules/log2.csv | 6 | 0 | 0 | MATCH |
| src/test/scala/tests/test51_sttt_rules/spec.qtl | src/test/scala/tests/test51_sttt_rules/log3.csv | 3 | 0 | 0 | MATCH |
