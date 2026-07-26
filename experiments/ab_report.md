# A/B validation: DejaVu vs DejaVuMT

solver: z3; max events/log: 1000; pairs: 333; wall time: 2090s

## Summary

- MATCH: 193
- MT_TIMEOUT: 13
- SKIP_UNSUPPORTED: 127

The 13 MT_TIMEOUT pairs (file/prop, locks/dataraces, test18_gc spec4+5,
test2_fmcad_file — quantifier-heavy specs whose qe2 cost grows with the
accumulated formula) were rerun at 300-event prefixes with a 300s timeout:
**all 13 MATCH**.  Total: 206 comparable pairs, 206 identical verdicts,
0 mismatches.  Skips: 66 lowercase-quantifier, 59 rules, 2 empty spec
(test29_renaming/spec2.qtl).  (The three test52 Z[<=10] pairs, previously
skipped, MATCH since Z was implemented: 0, 2 and 3 violations respectively,
identical in both tools.)

## Pairs

| spec | log | events | dejavu viol | mt viol | status |
|---|---|---|---|---|---|
| out/examples/access/prop1.qtl | out/examples/access/log1.csv | 8 | 1 | 1 | MATCH |
| out/examples/access/prop1.qtl | out/examples/access/log2.csv | 1000 | 0 | 0 | MATCH |
| out/examples/access/prop1.qtl | out/examples/access/log3.csv | 1000 | 0 | 0 | MATCH |
| out/examples/access/prop1.qtl | out/examples/access/log4.csv | 1000 | 0 | 0 | MATCH |
| out/examples/access/prop2.qtl | out/examples/access/log1.csv | 8 | 1 | 1 | MATCH |
| out/examples/access/prop2.qtl | out/examples/access/log2.csv | 1000 | 0 | 0 | MATCH |
| out/examples/access/prop2.qtl | out/examples/access/log3.csv | 1000 | 0 | 0 | MATCH |
| out/examples/access/prop2.qtl | out/examples/access/log4.csv | 1000 | 0 | 0 | MATCH |
| out/examples/auction/prop1.qtl | out/examples/auction/log1.csv | 12 | 1 | 1 | MATCH |
| out/examples/auction/prop2.qtl | out/examples/auction/log1.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| out/examples/auction/prop3.qtl | out/examples/auction/log1.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| out/examples/auction/prop4.qtl | out/examples/auction/log1.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| out/examples/file/prop.qtl | out/examples/file/log1.csv | 10 | 1 | 1 | MATCH |
| out/examples/file/prop.qtl | out/examples/file/log2.csv | 1000 | 0 |  | MT_TIMEOUT (timeout) |
| out/examples/file/prop.qtl | out/examples/file/log3.csv | 1000 | 0 |  | MT_TIMEOUT (timeout) |
| out/examples/file/prop.qtl | out/examples/file/log4.csv | 1000 | 0 |  | MT_TIMEOUT (timeout) |
| out/examples/gc/prop1.qtl | out/examples/gc/log1.csv | 14 | 0 | 0 | MATCH |
| out/examples/gc/prop2.qtl | out/examples/gc/log1.csv | 14 | 0 | 0 | MATCH |
| out/examples/gc/prop3.qtl | out/examples/gc/log1.csv | 14 | 0 | 0 | MATCH |
| out/examples/gc/prop4.qtl | out/examples/gc/log1.csv | 14 | 0 | 0 | MATCH |
| out/examples/locks/basic/prop.qtl | out/examples/locks/basic/log1.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| out/examples/locks/basic/prop.qtl | out/examples/locks/basic/log2.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| out/examples/locks/basic/prop.qtl | out/examples/locks/basic/log3.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| out/examples/locks/basic/prop.qtl | out/examples/locks/basic/log4.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| out/examples/locks/dataraces/prop.qtl | out/examples/locks/dataraces/log1.csv | 11 | 1 | 1 | MATCH |
| out/examples/locks/dataraces/prop.qtl | out/examples/locks/dataraces/log2.csv | 1000 | 0 |  | MT_TIMEOUT (timeout) |
| out/examples/locks/dataraces/prop.qtl | out/examples/locks/dataraces/log3.csv | 1000 | 0 |  | MT_TIMEOUT (timeout) |
| out/examples/locks/dataraces/prop.qtl | out/examples/locks/dataraces/log4.csv | 1000 | 0 |  | MT_TIMEOUT (timeout) |
| out/examples/locks/deadlocks/prop.qtl | out/examples/locks/deadlocks/log1.csv | 8 | 1 | 1 | MATCH |
| out/examples/locks/deadlocks/prop.qtl | out/examples/locks/deadlocks/log2.csv | 1000 | 0 | 0 | MATCH |
| out/examples/locks/deadlocks/prop.qtl | out/examples/locks/deadlocks/log3.csv | 1000 | 0 | 0 | MATCH |
| out/examples/locks/deadlocks/prop.qtl | out/examples/locks/deadlocks/log4.csv | 1000 | 0 | 0 | MATCH |
| out/examples/password/prop.qtl | out/examples/password/log1.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| out/examples/taskspawning/prop.qtl | out/examples/taskspawning/biglog10k.csv |  |  |  | SKIP_UNSUPPORTED (rules) |
| out/examples/taskspawning/prop.qtl | out/examples/taskspawning/biglog20k.csv |  |  |  | SKIP_UNSUPPORTED (rules) |
| out/examples/taskspawning/prop.qtl | out/examples/taskspawning/biglog40k.csv |  |  |  | SKIP_UNSUPPORTED (rules) |
| out/examples/taskspawning/prop.qtl | out/examples/taskspawning/log1.csv |  |  |  | SKIP_UNSUPPORTED (rules) |
| out/examples/taskspawning/prop.qtl | out/examples/taskspawning/log2.csv |  |  |  | SKIP_UNSUPPORTED (rules) |
| out/examples/telemetry/prop1.qtl | out/examples/telemetry/biglog10000k.csv |  |  |  | SKIP_UNSUPPORTED (rules) |
| out/examples/telemetry/prop1.qtl | out/examples/telemetry/biglog1000k.csv |  |  |  | SKIP_UNSUPPORTED (rules) |
| out/examples/telemetry/prop1.qtl | out/examples/telemetry/biglog100k.csv |  |  |  | SKIP_UNSUPPORTED (rules) |
| out/examples/telemetry/prop1.qtl | out/examples/telemetry/biglog5000k.csv |  |  |  | SKIP_UNSUPPORTED (rules) |
| out/examples/telemetry/prop1.qtl | out/examples/telemetry/log1.csv |  |  |  | SKIP_UNSUPPORTED (rules) |
| out/examples/telemetry/prop1.qtl | out/examples/telemetry/log2.csv |  |  |  | SKIP_UNSUPPORTED (rules) |
| out/examples/telemetry/prop1.qtl | out/examples/telemetry/log3.csv |  |  |  | SKIP_UNSUPPORTED (rules) |
| out/examples/telemetry/prop2.qtl | out/examples/telemetry/biglog10000k.csv |  |  |  | SKIP_UNSUPPORTED (rules) |
| out/examples/telemetry/prop2.qtl | out/examples/telemetry/biglog1000k.csv |  |  |  | SKIP_UNSUPPORTED (rules) |
| out/examples/telemetry/prop2.qtl | out/examples/telemetry/biglog100k.csv |  |  |  | SKIP_UNSUPPORTED (rules) |
| out/examples/telemetry/prop2.qtl | out/examples/telemetry/biglog5000k.csv |  |  |  | SKIP_UNSUPPORTED (rules) |
| out/examples/telemetry/prop2.qtl | out/examples/telemetry/log1.csv |  |  |  | SKIP_UNSUPPORTED (rules) |
| out/examples/telemetry/prop2.qtl | out/examples/telemetry/log2.csv |  |  |  | SKIP_UNSUPPORTED (rules) |
| out/examples/telemetry/prop2.qtl | out/examples/telemetry/log3.csv |  |  |  | SKIP_UNSUPPORTED (rules) |
| out/examples/unsafemapit/prop.qtl | out/examples/unsafemapit/log1.csv | 14 | 1 | 1 | MATCH |
| src/test/scala/tests/test10/spec.qtl | src/test/scala/tests/test10/log1.csv | 7 | 0 | 0 | MATCH |
| src/test/scala/tests/test10/spec.qtl | src/test/scala/tests/test10/log2.csv | 8 | 0 | 0 | MATCH |
| src/test/scala/tests/test10/spec.qtl | src/test/scala/tests/test10/log3.csv | 8 | 1 | 1 | MATCH |
| src/test/scala/tests/test10/spec.qtl | src/test/scala/tests/test10/log4.csv | 1000 | 0 | 0 | MATCH |
| src/test/scala/tests/test10/spec.qtl | src/test/scala/tests/test10/log5.csv | 13 | 1 | 1 | MATCH |
| src/test/scala/tests/test10/spec.qtl | src/test/scala/tests/test10/log6.csv | 17 | 2 | 2 | MATCH |
| src/test/scala/tests/test11/spec1.qtl | src/test/scala/tests/test11/log1.csv | 7 | 0 | 0 | MATCH |
| src/test/scala/tests/test11/spec1.qtl | src/test/scala/tests/test11/log2.csv | 6 | 0 | 0 | MATCH |
| src/test/scala/tests/test11/spec2.qtl | src/test/scala/tests/test11/log1.csv | 7 | 0 | 0 | MATCH |
| src/test/scala/tests/test11/spec2.qtl | src/test/scala/tests/test11/log2.csv | 6 | 0 | 0 | MATCH |
| src/test/scala/tests/test11/spec3.qtl | src/test/scala/tests/test11/log1.csv | 7 | 0 | 0 | MATCH |
| src/test/scala/tests/test11/spec3.qtl | src/test/scala/tests/test11/log2.csv | 6 | 0 | 0 | MATCH |
| src/test/scala/tests/test11/spec4.qtl | src/test/scala/tests/test11/log1.csv | 7 | 2 | 2 | MATCH |
| src/test/scala/tests/test11/spec4.qtl | src/test/scala/tests/test11/log2.csv | 6 | 0 | 0 | MATCH |
| src/test/scala/tests/test12/spec.qtl | src/test/scala/tests/test12/log1.csv | 3 | 2 | 2 | MATCH |
| src/test/scala/tests/test12/spec.qtl | src/test/scala/tests/test12/log2.csv | 3 | 3 | 3 | MATCH |
| src/test/scala/tests/test13/spec.qtl | src/test/scala/tests/test13/log1.csv | 2 | 2 | 2 | MATCH |
| src/test/scala/tests/test13/spec.qtl | src/test/scala/tests/test13/log2.csv | 2 | 2 | 2 | MATCH |
| src/test/scala/tests/test14/spec.qtl | src/test/scala/tests/test14/log1.csv | 5 | 3 | 3 | MATCH |
| src/test/scala/tests/test14/spec.qtl | src/test/scala/tests/test14/log2.csv | 6 | 5 | 5 | MATCH |
| src/test/scala/tests/test15/spec.qtl | src/test/scala/tests/test15/log1.csv | 11 | 5 | 5 | MATCH |
| src/test/scala/tests/test15/spec.qtl | src/test/scala/tests/test15/log2.csv | 10 | 8 | 8 | MATCH |
| src/test/scala/tests/test16/spec1.qtl | src/test/scala/tests/test16/log1.csv | 7 | 7 | 7 | MATCH |
| src/test/scala/tests/test16/spec1.qtl | src/test/scala/tests/test16/log2.csv | 8 | 8 | 8 | MATCH |
| src/test/scala/tests/test16/spec2.qtl | src/test/scala/tests/test16/log1.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| src/test/scala/tests/test16/spec2.qtl | src/test/scala/tests/test16/log2.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| src/test/scala/tests/test17/spec.qtl | src/test/scala/tests/test17/log1.csv | 8 | 2 | 2 | MATCH |
| src/test/scala/tests/test17/spec.qtl | src/test/scala/tests/test17/log2.csv | 8 | 4 | 4 | MATCH |
| src/test/scala/tests/test18_gc/spec1.qtl | src/test/scala/tests/test18_gc/log1.csv | 14 | 0 | 0 | MATCH |
| src/test/scala/tests/test18_gc/spec1.qtl | src/test/scala/tests/test18_gc/log2.csv | 1000 | 0 | 0 | MATCH |
| src/test/scala/tests/test18_gc/spec1.qtl | src/test/scala/tests/test18_gc/log3.csv | 1000 | 0 | 0 | MATCH |
| src/test/scala/tests/test18_gc/spec1.qtl | src/test/scala/tests/test18_gc/log4.csv | 1000 | 0 | 0 | MATCH |
| src/test/scala/tests/test18_gc/spec1.qtl | src/test/scala/tests/test18_gc/log5.csv | 1000 | 0 | 0 | MATCH |
| src/test/scala/tests/test18_gc/spec2.qtl | src/test/scala/tests/test18_gc/log1.csv | 14 | 0 | 0 | MATCH |
| src/test/scala/tests/test18_gc/spec2.qtl | src/test/scala/tests/test18_gc/log2.csv | 1000 | 0 | 0 | MATCH |
| src/test/scala/tests/test18_gc/spec2.qtl | src/test/scala/tests/test18_gc/log3.csv | 1000 | 0 | 0 | MATCH |
| src/test/scala/tests/test18_gc/spec2.qtl | src/test/scala/tests/test18_gc/log4.csv | 1000 | 0 | 0 | MATCH |
| src/test/scala/tests/test18_gc/spec2.qtl | src/test/scala/tests/test18_gc/log5.csv | 1000 | 0 | 0 | MATCH |
| src/test/scala/tests/test18_gc/spec3.qtl | src/test/scala/tests/test18_gc/log1.csv | 14 | 0 | 0 | MATCH |
| src/test/scala/tests/test18_gc/spec3.qtl | src/test/scala/tests/test18_gc/log2.csv | 1000 | 0 | 0 | MATCH |
| src/test/scala/tests/test18_gc/spec3.qtl | src/test/scala/tests/test18_gc/log3.csv | 1000 | 0 | 0 | MATCH |
| src/test/scala/tests/test18_gc/spec3.qtl | src/test/scala/tests/test18_gc/log4.csv | 1000 | 0 | 0 | MATCH |
| src/test/scala/tests/test18_gc/spec3.qtl | src/test/scala/tests/test18_gc/log5.csv | 1000 | 0 | 0 | MATCH |
| src/test/scala/tests/test18_gc/spec4.qtl | src/test/scala/tests/test18_gc/log1.csv | 14 | 0 | 0 | MATCH |
| src/test/scala/tests/test18_gc/spec4.qtl | src/test/scala/tests/test18_gc/log2.csv | 1000 | 0 |  | MT_TIMEOUT (timeout) |
| src/test/scala/tests/test18_gc/spec4.qtl | src/test/scala/tests/test18_gc/log3.csv | 1000 | 0 |  | MT_TIMEOUT (timeout) |
| src/test/scala/tests/test18_gc/spec4.qtl | src/test/scala/tests/test18_gc/log4.csv | 1000 | 0 | 0 | MATCH |
| src/test/scala/tests/test18_gc/spec4.qtl | src/test/scala/tests/test18_gc/log5.csv | 1000 | 0 | 0 | MATCH |
| src/test/scala/tests/test18_gc/spec5.qtl | src/test/scala/tests/test18_gc/log1.csv | 14 | 0 | 0 | MATCH |
| src/test/scala/tests/test18_gc/spec5.qtl | src/test/scala/tests/test18_gc/log2.csv | 1000 | 0 |  | MT_TIMEOUT (timeout) |
| src/test/scala/tests/test18_gc/spec5.qtl | src/test/scala/tests/test18_gc/log3.csv | 1000 | 0 |  | MT_TIMEOUT (timeout) |
| src/test/scala/tests/test18_gc/spec5.qtl | src/test/scala/tests/test18_gc/log4.csv | 1000 | 0 | 0 | MATCH |
| src/test/scala/tests/test18_gc/spec5.qtl | src/test/scala/tests/test18_gc/log5.csv | 1000 | 0 | 0 | MATCH |
| src/test/scala/tests/test19_relations/spec1.qtl | src/test/scala/tests/test19_relations/log1.csv | 12 | 1 | 1 | MATCH |
| src/test/scala/tests/test19_relations/spec2.qtl | src/test/scala/tests/test19_relations/log1.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| src/test/scala/tests/test19_relations/spec3.qtl | src/test/scala/tests/test19_relations/log1.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| src/test/scala/tests/test19_relations/spec4.qtl | src/test/scala/tests/test19_relations/log1.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| src/test/scala/tests/test1_fmcad_access/spec.qtl | src/test/scala/tests/test1_fmcad_access/log1.csv | 1000 | 0 | 0 | MATCH |
| src/test/scala/tests/test1_fmcad_access/spec.qtl | src/test/scala/tests/test1_fmcad_access/log2.csv | 1000 | 0 | 0 | MATCH |
| src/test/scala/tests/test1_fmcad_access/spec.qtl | src/test/scala/tests/test1_fmcad_access/log3.csv | 1000 | 0 | 0 | MATCH |
| src/test/scala/tests/test20/spec1.qtl | src/test/scala/tests/test20/log1.csv | 8 | 1 | 1 | MATCH |
| src/test/scala/tests/test20/spec1.qtl | src/test/scala/tests/test20/log2.csv | 11 | 0 | 0 | MATCH |
| src/test/scala/tests/test20/spec1.qtl | src/test/scala/tests/test20/log3.csv | 8 | 0 | 0 | MATCH |
| src/test/scala/tests/test20/spec1.qtl | src/test/scala/tests/test20/log4.csv | 4 | 0 | 0 | MATCH |
| src/test/scala/tests/test20/spec2.qtl | src/test/scala/tests/test20/log1.csv | 8 | 1 | 1 | MATCH |
| src/test/scala/tests/test20/spec2.qtl | src/test/scala/tests/test20/log2.csv | 11 | 0 | 0 | MATCH |
| src/test/scala/tests/test20/spec2.qtl | src/test/scala/tests/test20/log3.csv | 8 | 0 | 0 | MATCH |
| src/test/scala/tests/test20/spec2.qtl | src/test/scala/tests/test20/log4.csv | 4 | 0 | 0 | MATCH |
| src/test/scala/tests/test20/spec3.qtl | src/test/scala/tests/test20/log1.csv | 8 | 0 | 0 | MATCH |
| src/test/scala/tests/test20/spec3.qtl | src/test/scala/tests/test20/log2.csv | 11 | 1 | 1 | MATCH |
| src/test/scala/tests/test20/spec3.qtl | src/test/scala/tests/test20/log3.csv | 8 | 0 | 0 | MATCH |
| src/test/scala/tests/test20/spec3.qtl | src/test/scala/tests/test20/log4.csv | 4 | 0 | 0 | MATCH |
| src/test/scala/tests/test20/spec4.qtl | src/test/scala/tests/test20/log1.csv | 8 | 0 | 0 | MATCH |
| src/test/scala/tests/test20/spec4.qtl | src/test/scala/tests/test20/log2.csv | 11 | 1 | 1 | MATCH |
| src/test/scala/tests/test20/spec4.qtl | src/test/scala/tests/test20/log3.csv | 8 | 0 | 0 | MATCH |
| src/test/scala/tests/test20/spec4.qtl | src/test/scala/tests/test20/log4.csv | 4 | 0 | 0 | MATCH |
| src/test/scala/tests/test20/spec5.qtl | src/test/scala/tests/test20/log1.csv | 8 | 0 | 0 | MATCH |
| src/test/scala/tests/test20/spec5.qtl | src/test/scala/tests/test20/log2.csv | 11 | 0 | 0 | MATCH |
| src/test/scala/tests/test20/spec5.qtl | src/test/scala/tests/test20/log3.csv | 8 | 1 | 1 | MATCH |
| src/test/scala/tests/test20/spec5.qtl | src/test/scala/tests/test20/log4.csv | 4 | 1 | 1 | MATCH |
| src/test/scala/tests/test21_msl/spec1.qtl | src/test/scala/tests/test21_msl/log1.csv | 8 | 1 | 1 | MATCH |
| src/test/scala/tests/test21_msl/spec1.qtl | src/test/scala/tests/test21_msl/log2.csv | 50 | 23 | 23 | MATCH |
| src/test/scala/tests/test21_msl/spec1.qtl | src/test/scala/tests/test21_msl/log3.csv | 50 | 0 | 0 | MATCH |
| src/test/scala/tests/test21_msl/spec1.qtl | src/test/scala/tests/test21_msl/log4.csv | 6 | 1 | 1 | MATCH |
| src/test/scala/tests/test21_msl/spec1.qtl | src/test/scala/tests/test21_msl/log5.csv | 6 | 0 | 0 | MATCH |
| src/test/scala/tests/test21_msl/spec1.qtl | src/test/scala/tests/test21_msl/log_msl.csv | 1000 | 0 | 0 | MATCH |
| src/test/scala/tests/test21_msl/spec1.qtl | src/test/scala/tests/test21_msl/log_msl_timed.csv | 1000 | 0 | 0 | MATCH |
| src/test/scala/tests/test21_msl/spec1_timed.qtl | src/test/scala/tests/test21_msl/log1.csv | 8 | 0 | 0 | MATCH |
| src/test/scala/tests/test21_msl/spec1_timed.qtl | src/test/scala/tests/test21_msl/log2.csv | 50 | 0 | 0 | MATCH |
| src/test/scala/tests/test21_msl/spec1_timed.qtl | src/test/scala/tests/test21_msl/log3.csv | 50 | 28 | 28 | MATCH |
| src/test/scala/tests/test21_msl/spec1_timed.qtl | src/test/scala/tests/test21_msl/log4.csv | 6 | 0 | 0 | MATCH |
| src/test/scala/tests/test21_msl/spec1_timed.qtl | src/test/scala/tests/test21_msl/log5.csv | 6 | 2 | 2 | MATCH |
| src/test/scala/tests/test21_msl/spec1_timed.qtl | src/test/scala/tests/test21_msl/log_msl.csv | 1000 | 0 | 0 | MATCH |
| src/test/scala/tests/test21_msl/spec1_timed.qtl | src/test/scala/tests/test21_msl/log_msl_timed.csv | 1000 | 0 | 0 | MATCH |
| src/test/scala/tests/test21_msl/spec2.qtl | src/test/scala/tests/test21_msl/log1.csv | 8 | 0 | 0 | MATCH |
| src/test/scala/tests/test21_msl/spec2.qtl | src/test/scala/tests/test21_msl/log2.csv | 50 | 0 | 0 | MATCH |
| src/test/scala/tests/test21_msl/spec2.qtl | src/test/scala/tests/test21_msl/log3.csv | 50 | 0 | 0 | MATCH |
| src/test/scala/tests/test21_msl/spec2.qtl | src/test/scala/tests/test21_msl/log4.csv | 6 | 0 | 0 | MATCH |
| src/test/scala/tests/test21_msl/spec2.qtl | src/test/scala/tests/test21_msl/log5.csv | 6 | 0 | 0 | MATCH |
| src/test/scala/tests/test21_msl/spec2.qtl | src/test/scala/tests/test21_msl/log_msl.csv | 1000 | 0 | 0 | MATCH |
| src/test/scala/tests/test21_msl/spec2.qtl | src/test/scala/tests/test21_msl/log_msl_timed.csv | 1000 | 0 | 0 | MATCH |
| src/test/scala/tests/test22_fmsd_unsafemapit/spec1.qtl | src/test/scala/tests/test22_fmsd_unsafemapit/log1.csv | 10 | 0 | 0 | MATCH |
| src/test/scala/tests/test22_fmsd_unsafemapit/spec1.qtl | src/test/scala/tests/test22_fmsd_unsafemapit/log2.csv | 11 | 1 | 1 | MATCH |
| src/test/scala/tests/test22_fmsd_unsafemapit/spec1.qtl | src/test/scala/tests/test22_fmsd_unsafemapit/log3.csv | 14 | 1 | 1 | MATCH |
| src/test/scala/tests/test22_fmsd_unsafemapit/spec1.qtl | src/test/scala/tests/test22_fmsd_unsafemapit/log4.csv | 5 | 0 | 0 | MATCH |
| src/test/scala/tests/test22_fmsd_unsafemapit/spec1.qtl | src/test/scala/tests/test22_fmsd_unsafemapit/log5.csv | 1000 | 0 | 0 | MATCH |
| src/test/scala/tests/test22_fmsd_unsafemapit/spec2.qtl | src/test/scala/tests/test22_fmsd_unsafemapit/log1.csv | 10 | 0 | 0 | MATCH |
| src/test/scala/tests/test22_fmsd_unsafemapit/spec2.qtl | src/test/scala/tests/test22_fmsd_unsafemapit/log2.csv | 11 | 1 | 1 | MATCH |
| src/test/scala/tests/test22_fmsd_unsafemapit/spec2.qtl | src/test/scala/tests/test22_fmsd_unsafemapit/log3.csv | 14 | 1 | 1 | MATCH |
| src/test/scala/tests/test22_fmsd_unsafemapit/spec2.qtl | src/test/scala/tests/test22_fmsd_unsafemapit/log4.csv | 5 | 1 | 1 | MATCH |
| src/test/scala/tests/test22_fmsd_unsafemapit/spec2.qtl | src/test/scala/tests/test22_fmsd_unsafemapit/log5.csv | 1000 | 0 | 0 | MATCH |
| src/test/scala/tests/test23_fmsd_locks/spec1.qtl | src/test/scala/tests/test23_fmsd_locks/log1.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| src/test/scala/tests/test23_fmsd_locks/spec1.qtl | src/test/scala/tests/test23_fmsd_locks/log10.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| src/test/scala/tests/test23_fmsd_locks/spec1.qtl | src/test/scala/tests/test23_fmsd_locks/log11.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| src/test/scala/tests/test23_fmsd_locks/spec1.qtl | src/test/scala/tests/test23_fmsd_locks/log12.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| src/test/scala/tests/test23_fmsd_locks/spec1.qtl | src/test/scala/tests/test23_fmsd_locks/log2.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| src/test/scala/tests/test23_fmsd_locks/spec1.qtl | src/test/scala/tests/test23_fmsd_locks/log3.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| src/test/scala/tests/test23_fmsd_locks/spec1.qtl | src/test/scala/tests/test23_fmsd_locks/log4.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| src/test/scala/tests/test23_fmsd_locks/spec1.qtl | src/test/scala/tests/test23_fmsd_locks/log5.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| src/test/scala/tests/test23_fmsd_locks/spec1.qtl | src/test/scala/tests/test23_fmsd_locks/log6.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| src/test/scala/tests/test23_fmsd_locks/spec1.qtl | src/test/scala/tests/test23_fmsd_locks/log7.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| src/test/scala/tests/test23_fmsd_locks/spec1.qtl | src/test/scala/tests/test23_fmsd_locks/log8.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| src/test/scala/tests/test23_fmsd_locks/spec1.qtl | src/test/scala/tests/test23_fmsd_locks/log9.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| src/test/scala/tests/test23_fmsd_locks/spec2.qtl | src/test/scala/tests/test23_fmsd_locks/log1.csv | 7 | 0 | 0 | MATCH |
| src/test/scala/tests/test23_fmsd_locks/spec2.qtl | src/test/scala/tests/test23_fmsd_locks/log10.csv | 9 | 0 | 0 | MATCH |
| src/test/scala/tests/test23_fmsd_locks/spec2.qtl | src/test/scala/tests/test23_fmsd_locks/log11.csv | 11 | 0 | 0 | MATCH |
| src/test/scala/tests/test23_fmsd_locks/spec2.qtl | src/test/scala/tests/test23_fmsd_locks/log12.csv | 37 | 0 | 0 | MATCH |
| src/test/scala/tests/test23_fmsd_locks/spec2.qtl | src/test/scala/tests/test23_fmsd_locks/log2.csv | 11 | 0 | 0 | MATCH |
| src/test/scala/tests/test23_fmsd_locks/spec2.qtl | src/test/scala/tests/test23_fmsd_locks/log3.csv | 9 | 0 | 0 | MATCH |
| src/test/scala/tests/test23_fmsd_locks/spec2.qtl | src/test/scala/tests/test23_fmsd_locks/log4.csv | 13 | 1 | 1 | MATCH |
| src/test/scala/tests/test23_fmsd_locks/spec2.qtl | src/test/scala/tests/test23_fmsd_locks/log5.csv | 18 | 0 | 0 | MATCH |
| src/test/scala/tests/test23_fmsd_locks/spec2.qtl | src/test/scala/tests/test23_fmsd_locks/log6.csv | 18 | 0 | 0 | MATCH |
| src/test/scala/tests/test23_fmsd_locks/spec2.qtl | src/test/scala/tests/test23_fmsd_locks/log7.csv | 10 | 0 | 0 | MATCH |
| src/test/scala/tests/test23_fmsd_locks/spec2.qtl | src/test/scala/tests/test23_fmsd_locks/log8.csv | 6 | 0 | 0 | MATCH |
| src/test/scala/tests/test23_fmsd_locks/spec2.qtl | src/test/scala/tests/test23_fmsd_locks/log9.csv | 7 | 0 | 0 | MATCH |
| src/test/scala/tests/test23_fmsd_locks/spec3.qtl | src/test/scala/tests/test23_fmsd_locks/log1.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| src/test/scala/tests/test23_fmsd_locks/spec3.qtl | src/test/scala/tests/test23_fmsd_locks/log10.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| src/test/scala/tests/test23_fmsd_locks/spec3.qtl | src/test/scala/tests/test23_fmsd_locks/log11.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| src/test/scala/tests/test23_fmsd_locks/spec3.qtl | src/test/scala/tests/test23_fmsd_locks/log12.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| src/test/scala/tests/test23_fmsd_locks/spec3.qtl | src/test/scala/tests/test23_fmsd_locks/log2.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| src/test/scala/tests/test23_fmsd_locks/spec3.qtl | src/test/scala/tests/test23_fmsd_locks/log3.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| src/test/scala/tests/test23_fmsd_locks/spec3.qtl | src/test/scala/tests/test23_fmsd_locks/log4.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| src/test/scala/tests/test23_fmsd_locks/spec3.qtl | src/test/scala/tests/test23_fmsd_locks/log5.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| src/test/scala/tests/test23_fmsd_locks/spec3.qtl | src/test/scala/tests/test23_fmsd_locks/log6.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| src/test/scala/tests/test23_fmsd_locks/spec3.qtl | src/test/scala/tests/test23_fmsd_locks/log7.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| src/test/scala/tests/test23_fmsd_locks/spec3.qtl | src/test/scala/tests/test23_fmsd_locks/log8.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| src/test/scala/tests/test23_fmsd_locks/spec3.qtl | src/test/scala/tests/test23_fmsd_locks/log9.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| src/test/scala/tests/test23_fmsd_locks/spec4.qtl | src/test/scala/tests/test23_fmsd_locks/log1.csv | 7 | 0 | 0 | MATCH |
| src/test/scala/tests/test23_fmsd_locks/spec4.qtl | src/test/scala/tests/test23_fmsd_locks/log10.csv | 9 | 0 | 0 | MATCH |
| src/test/scala/tests/test23_fmsd_locks/spec4.qtl | src/test/scala/tests/test23_fmsd_locks/log11.csv | 11 | 0 | 0 | MATCH |
| src/test/scala/tests/test23_fmsd_locks/spec4.qtl | src/test/scala/tests/test23_fmsd_locks/log12.csv | 37 | 1 | 1 | MATCH |
| src/test/scala/tests/test23_fmsd_locks/spec4.qtl | src/test/scala/tests/test23_fmsd_locks/log2.csv | 11 | 0 | 0 | MATCH |
| src/test/scala/tests/test23_fmsd_locks/spec4.qtl | src/test/scala/tests/test23_fmsd_locks/log3.csv | 9 | 0 | 0 | MATCH |
| src/test/scala/tests/test23_fmsd_locks/spec4.qtl | src/test/scala/tests/test23_fmsd_locks/log4.csv | 13 | 0 | 0 | MATCH |
| src/test/scala/tests/test23_fmsd_locks/spec4.qtl | src/test/scala/tests/test23_fmsd_locks/log5.csv | 18 | 0 | 0 | MATCH |
| src/test/scala/tests/test23_fmsd_locks/spec4.qtl | src/test/scala/tests/test23_fmsd_locks/log6.csv | 18 | 0 | 0 | MATCH |
| src/test/scala/tests/test23_fmsd_locks/spec4.qtl | src/test/scala/tests/test23_fmsd_locks/log7.csv | 10 | 0 | 0 | MATCH |
| src/test/scala/tests/test23_fmsd_locks/spec4.qtl | src/test/scala/tests/test23_fmsd_locks/log8.csv | 6 | 2 | 2 | MATCH |
| src/test/scala/tests/test23_fmsd_locks/spec4.qtl | src/test/scala/tests/test23_fmsd_locks/log9.csv | 7 | 1 | 1 | MATCH |
| src/test/scala/tests/test23_fmsd_locks/spec5.qtl | src/test/scala/tests/test23_fmsd_locks/log1.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| src/test/scala/tests/test23_fmsd_locks/spec5.qtl | src/test/scala/tests/test23_fmsd_locks/log10.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| src/test/scala/tests/test23_fmsd_locks/spec5.qtl | src/test/scala/tests/test23_fmsd_locks/log11.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| src/test/scala/tests/test23_fmsd_locks/spec5.qtl | src/test/scala/tests/test23_fmsd_locks/log12.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| src/test/scala/tests/test23_fmsd_locks/spec5.qtl | src/test/scala/tests/test23_fmsd_locks/log2.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| src/test/scala/tests/test23_fmsd_locks/spec5.qtl | src/test/scala/tests/test23_fmsd_locks/log3.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| src/test/scala/tests/test23_fmsd_locks/spec5.qtl | src/test/scala/tests/test23_fmsd_locks/log4.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| src/test/scala/tests/test23_fmsd_locks/spec5.qtl | src/test/scala/tests/test23_fmsd_locks/log5.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| src/test/scala/tests/test23_fmsd_locks/spec5.qtl | src/test/scala/tests/test23_fmsd_locks/log6.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| src/test/scala/tests/test23_fmsd_locks/spec5.qtl | src/test/scala/tests/test23_fmsd_locks/log7.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| src/test/scala/tests/test23_fmsd_locks/spec5.qtl | src/test/scala/tests/test23_fmsd_locks/log8.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| src/test/scala/tests/test23_fmsd_locks/spec5.qtl | src/test/scala/tests/test23_fmsd_locks/log9.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| src/test/scala/tests/test24_macros/spec1.qtl | src/test/scala/tests/test24_macros/log1.csv | 7 | 0 | 0 | MATCH |
| src/test/scala/tests/test24_macros/spec1.qtl | src/test/scala/tests/test24_macros/log2.csv | 7 | 1 | 1 | MATCH |
| src/test/scala/tests/test24_macros/spec2.qtl | src/test/scala/tests/test24_macros/log1.csv | 7 | 0 | 0 | MATCH |
| src/test/scala/tests/test24_macros/spec2.qtl | src/test/scala/tests/test24_macros/log2.csv | 7 | 1 | 1 | MATCH |
| src/test/scala/tests/test25_macros/spec1.qtl | src/test/scala/tests/test25_macros/log1.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| src/test/scala/tests/test25_macros/spec1.qtl | src/test/scala/tests/test25_macros/log2.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| src/test/scala/tests/test25_macros/spec2.qtl | src/test/scala/tests/test25_macros/log1.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| src/test/scala/tests/test25_macros/spec2.qtl | src/test/scala/tests/test25_macros/log2.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| src/test/scala/tests/test25_macros/spec3.qtl | src/test/scala/tests/test25_macros/log1.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| src/test/scala/tests/test25_macros/spec3.qtl | src/test/scala/tests/test25_macros/log2.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| src/test/scala/tests/test26_propositional/spec1.qtl | src/test/scala/tests/test26_propositional/log1.csv | 9 | 0 | 0 | MATCH |
| src/test/scala/tests/test26_propositional/spec1.qtl | src/test/scala/tests/test26_propositional/log2.csv | 9 | 1 | 1 | MATCH |
| src/test/scala/tests/test26_propositional/spec1.qtl | src/test/scala/tests/test26_propositional/log3.csv | 7 | 0 | 0 | MATCH |
| src/test/scala/tests/test26_propositional/spec1.qtl | src/test/scala/tests/test26_propositional/log4.csv | 7 | 0 | 0 | MATCH |
| src/test/scala/tests/test26_propositional/spec2.qtl | src/test/scala/tests/test26_propositional/log1.csv | 9 | 0 | 0 | MATCH |
| src/test/scala/tests/test26_propositional/spec2.qtl | src/test/scala/tests/test26_propositional/log2.csv | 9 | 0 | 0 | MATCH |
| src/test/scala/tests/test26_propositional/spec2.qtl | src/test/scala/tests/test26_propositional/log3.csv | 7 | 0 | 0 | MATCH |
| src/test/scala/tests/test26_propositional/spec2.qtl | src/test/scala/tests/test26_propositional/log4.csv | 7 | 1 | 1 | MATCH |
| src/test/scala/tests/test27_quantrenaming/spec1.qtl | src/test/scala/tests/test27_quantrenaming/log1.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| src/test/scala/tests/test27_quantrenaming/spec1.qtl | src/test/scala/tests/test27_quantrenaming/log2.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| src/test/scala/tests/test27_quantrenaming/spec2.qtl | src/test/scala/tests/test27_quantrenaming/log1.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| src/test/scala/tests/test27_quantrenaming/spec2.qtl | src/test/scala/tests/test27_quantrenaming/log2.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| src/test/scala/tests/test29_renaming/spec1.qtl | src/test/scala/tests/test29_renaming/log1.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| src/test/scala/tests/test29_renaming/spec1.qtl | src/test/scala/tests/test29_renaming/log2.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| src/test/scala/tests/test29_renaming/spec2.qtl | src/test/scala/tests/test29_renaming/log1.csv |  |  |  | SKIP_UNSUPPORTED (parse-error) |
| src/test/scala/tests/test29_renaming/spec2.qtl | src/test/scala/tests/test29_renaming/log2.csv |  |  |  | SKIP_UNSUPPORTED (parse-error) |
| src/test/scala/tests/test2_fmcad_file/spec.qtl | src/test/scala/tests/test2_fmcad_file/log1.csv | 1000 | 0 |  | MT_TIMEOUT (timeout) |
| src/test/scala/tests/test2_fmcad_file/spec.qtl | src/test/scala/tests/test2_fmcad_file/log2.csv | 1000 | 0 |  | MT_TIMEOUT (timeout) |
| src/test/scala/tests/test2_fmcad_file/spec.qtl | src/test/scala/tests/test2_fmcad_file/log3.csv | 1000 | 0 |  | MT_TIMEOUT (timeout) |
| src/test/scala/tests/test30_badpredicates/spec1.qtl | src/test/scala/tests/test30_badpredicates/log1.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| src/test/scala/tests/test30_badpredicates/spec2.qtl | src/test/scala/tests/test30_badpredicates/log1.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| src/test/scala/tests/test31_spin18/spec1.qtl | src/test/scala/tests/test31_spin18/log1.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| src/test/scala/tests/test31_spin18/spec1.qtl | src/test/scala/tests/test31_spin18/log2.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| src/test/scala/tests/test32_isola18/spec.qtl | src/test/scala/tests/test32_isola18/log1.csv | 9 | 0 | 0 | MATCH |
| src/test/scala/tests/test33_isola18_rv/spec.qtl | src/test/scala/tests/test33_isola18_rv/log1.csv | 2 | 1 | 1 | MATCH |
| src/test/scala/tests/test34_states/spec.qtl | src/test/scala/tests/test34_states/log1.csv |  |  |  | SKIP_UNSUPPORTED (rules) |
| src/test/scala/tests/test34_states/spec.qtl | src/test/scala/tests/test34_states/log2.csv |  |  |  | SKIP_UNSUPPORTED (rules) |
| src/test/scala/tests/test35_states/spec.qtl | src/test/scala/tests/test35_states/log1.csv |  |  |  | SKIP_UNSUPPORTED (rules) |
| src/test/scala/tests/test35_states/spec.qtl | src/test/scala/tests/test35_states/log2.csv |  |  |  | SKIP_UNSUPPORTED (rules) |
| src/test/scala/tests/test35_states/spec.qtl | src/test/scala/tests/test35_states/log3.csv |  |  |  | SKIP_UNSUPPORTED (rules) |
| src/test/scala/tests/test36_states/spec.qtl | src/test/scala/tests/test36_states/log1.csv |  |  |  | SKIP_UNSUPPORTED (rules) |
| src/test/scala/tests/test36_states/spec.qtl | src/test/scala/tests/test36_states/log2.csv |  |  |  | SKIP_UNSUPPORTED (rules) |
| src/test/scala/tests/test37_states/spec.qtl | src/test/scala/tests/test37_states/log1.csv |  |  |  | SKIP_UNSUPPORTED (rules) |
| src/test/scala/tests/test37_states/spec.qtl | src/test/scala/tests/test37_states/log2.csv |  |  |  | SKIP_UNSUPPORTED (rules) |
| src/test/scala/tests/test38_states/spec.qtl | src/test/scala/tests/test38_states/log1.csv |  |  |  | SKIP_UNSUPPORTED (rules) |
| src/test/scala/tests/test38_states/spec.qtl | src/test/scala/tests/test38_states/log2.csv |  |  |  | SKIP_UNSUPPORTED (rules) |
| src/test/scala/tests/test39_formalise_wolper/spec.qtl | src/test/scala/tests/test39_formalise_wolper/biglog10000k.csv |  |  |  | SKIP_UNSUPPORTED (rules) |
| src/test/scala/tests/test39_formalise_wolper/spec.qtl | src/test/scala/tests/test39_formalise_wolper/biglog1000k.csv |  |  |  | SKIP_UNSUPPORTED (rules) |
| src/test/scala/tests/test39_formalise_wolper/spec.qtl | src/test/scala/tests/test39_formalise_wolper/biglog100k.csv |  |  |  | SKIP_UNSUPPORTED (rules) |
| src/test/scala/tests/test39_formalise_wolper/spec.qtl | src/test/scala/tests/test39_formalise_wolper/biglog5000k.csv |  |  |  | SKIP_UNSUPPORTED (rules) |
| src/test/scala/tests/test39_formalise_wolper/spec.qtl | src/test/scala/tests/test39_formalise_wolper/log1.csv |  |  |  | SKIP_UNSUPPORTED (rules) |
| src/test/scala/tests/test39_formalise_wolper/spec.qtl | src/test/scala/tests/test39_formalise_wolper/log2.csv |  |  |  | SKIP_UNSUPPORTED (rules) |
| src/test/scala/tests/test39_formalise_wolper/spec.qtl | src/test/scala/tests/test39_formalise_wolper/log3.csv |  |  |  | SKIP_UNSUPPORTED (rules) |
| src/test/scala/tests/test3_fmcad_fifo/spec.qtl | src/test/scala/tests/test3_fmcad_fifo/log1.csv | 22 | 5 | 5 | MATCH |
| src/test/scala/tests/test3_fmcad_fifo/spec.qtl | src/test/scala/tests/test3_fmcad_fifo/log2.csv | 1000 | 0 | 0 | MATCH |
| src/test/scala/tests/test4/spec.qtl | src/test/scala/tests/test4/log1.csv | 5 | 0 | 0 | MATCH |
| src/test/scala/tests/test4/spec.qtl | src/test/scala/tests/test4/log2.csv | 6 | 1 | 1 | MATCH |
| src/test/scala/tests/test40_formalise_immigrant/spec.qtl | src/test/scala/tests/test40_formalise_immigrant/log1.csv |  |  |  | SKIP_UNSUPPORTED (rules) |
| src/test/scala/tests/test40_formalise_immigrant/spec.qtl | src/test/scala/tests/test40_formalise_immigrant/log2.csv |  |  |  | SKIP_UNSUPPORTED (rules) |
| src/test/scala/tests/test41_formalise_statemachine/spec.qtl | src/test/scala/tests/test41_formalise_statemachine/biglog10000k.csv |  |  |  | SKIP_UNSUPPORTED (rules) |
| src/test/scala/tests/test41_formalise_statemachine/spec.qtl | src/test/scala/tests/test41_formalise_statemachine/biglog1000k.csv |  |  |  | SKIP_UNSUPPORTED (rules) |
| src/test/scala/tests/test41_formalise_statemachine/spec.qtl | src/test/scala/tests/test41_formalise_statemachine/biglog100k.csv |  |  |  | SKIP_UNSUPPORTED (rules) |
| src/test/scala/tests/test41_formalise_statemachine/spec.qtl | src/test/scala/tests/test41_formalise_statemachine/biglog5000k.csv |  |  |  | SKIP_UNSUPPORTED (rules) |
| src/test/scala/tests/test41_formalise_statemachine/spec.qtl | src/test/scala/tests/test41_formalise_statemachine/log1.csv |  |  |  | SKIP_UNSUPPORTED (rules) |
| src/test/scala/tests/test41_formalise_statemachine/spec.qtl | src/test/scala/tests/test41_formalise_statemachine/log2.csv |  |  |  | SKIP_UNSUPPORTED (rules) |
| src/test/scala/tests/test42_formalise_taskspawning/spec.qtl | src/test/scala/tests/test42_formalise_taskspawning/biglog10k.csv |  |  |  | SKIP_UNSUPPORTED (rules) |
| src/test/scala/tests/test42_formalise_taskspawning/spec.qtl | src/test/scala/tests/test42_formalise_taskspawning/biglog20k.csv |  |  |  | SKIP_UNSUPPORTED (rules) |
| src/test/scala/tests/test42_formalise_taskspawning/spec.qtl | src/test/scala/tests/test42_formalise_taskspawning/biglog40k.csv |  |  |  | SKIP_UNSUPPORTED (rules) |
| src/test/scala/tests/test42_formalise_taskspawning/spec.qtl | src/test/scala/tests/test42_formalise_taskspawning/log1.csv |  |  |  | SKIP_UNSUPPORTED (rules) |
| src/test/scala/tests/test42_formalise_taskspawning/spec.qtl | src/test/scala/tests/test42_formalise_taskspawning/log2.csv |  |  |  | SKIP_UNSUPPORTED (rules) |
| src/test/scala/tests/test43_taskspawning/spec.qtl | src/test/scala/tests/test43_taskspawning/log1.csv |  |  |  | SKIP_UNSUPPORTED (rules) |
| src/test/scala/tests/test43_taskspawning/spec.qtl | src/test/scala/tests/test43_taskspawning/log2.csv |  |  |  | SKIP_UNSUPPORTED (rules) |
| src/test/scala/tests/test44_taskspawning/spec.qtl | src/test/scala/tests/test44_taskspawning/log1.csv |  |  |  | SKIP_UNSUPPORTED (rules) |
| src/test/scala/tests/test44_taskspawning/spec.qtl | src/test/scala/tests/test44_taskspawning/log2.csv |  |  |  | SKIP_UNSUPPORTED (rules) |
| src/test/scala/tests/test45_taskspawning_macros/spec.qtl | src/test/scala/tests/test45_taskspawning_macros/log1.csv |  |  |  | SKIP_UNSUPPORTED (rules) |
| src/test/scala/tests/test45_taskspawning_macros/spec.qtl | src/test/scala/tests/test45_taskspawning_macros/log2.csv |  |  |  | SKIP_UNSUPPORTED (rules) |
| src/test/scala/tests/test47_time/spec.qtl | src/test/scala/tests/test47_time/log1.timed.csv | 8 | 2 | 2 | MATCH |
| src/test/scala/tests/test48_time/spec.qtl | src/test/scala/tests/test48_time/log1.timed.csv |  |  |  | SKIP_UNSUPPORTED (lowercase-quantifier) |
| src/test/scala/tests/test49_time/spec1.qtl | src/test/scala/tests/test49_time/log1.timed.csv | 5 | 0 | 0 | MATCH |
| src/test/scala/tests/test49_time/spec2.qtl | src/test/scala/tests/test49_time/log1.timed.csv | 5 | 0 | 0 | MATCH |
| src/test/scala/tests/test5/spec.qtl | src/test/scala/tests/test5/log1.csv | 5 | 1 | 1 | MATCH |
| src/test/scala/tests/test5/spec.qtl | src/test/scala/tests/test5/log2.csv | 6 | 0 | 0 | MATCH |
| src/test/scala/tests/test50_sttt_rules/spec.qtl | src/test/scala/tests/test50_sttt_rules/log1.csv | 6 | 0 | 0 | MATCH |
| src/test/scala/tests/test50_sttt_rules/spec.qtl | src/test/scala/tests/test50_sttt_rules/log2.csv | 6 | 1 | 1 | MATCH |
| src/test/scala/tests/test51_sttt_rules/spec.qtl | src/test/scala/tests/test51_sttt_rules/log1.csv |  |  |  | SKIP_UNSUPPORTED (rules) |
| src/test/scala/tests/test51_sttt_rules/spec.qtl | src/test/scala/tests/test51_sttt_rules/log2.csv |  |  |  | SKIP_UNSUPPORTED (rules) |
| src/test/scala/tests/test51_sttt_rules/spec.qtl | src/test/scala/tests/test51_sttt_rules/log3.csv |  |  |  | SKIP_UNSUPPORTED (rules) |
| src/test/scala/tests/test52_time/spec.qtl | src/test/scala/tests/test52_time/log1.timed.csv | 5 | 0 | 0 | MATCH |
| src/test/scala/tests/test52_time/spec.qtl | src/test/scala/tests/test52_time/log2.timed.csv | 7 | 2 | 2 | MATCH |
| src/test/scala/tests/test52_time/spec.qtl | src/test/scala/tests/test52_time/log3.timed.csv | 13 | 3 | 3 | MATCH |
| src/test/scala/tests/test53_time/spec.qtl | src/test/scala/tests/test53_time/log1.timed.csv | 9 | 3 | 3 | MATCH |
| src/test/scala/tests/test54_time/spec1.qtl | src/test/scala/tests/test54_time/log1.timed.csv | 9 | 3 | 3 | MATCH |
| src/test/scala/tests/test54_time/spec2.qtl | src/test/scala/tests/test54_time/log1.timed.csv | 9 | 2 | 2 | MATCH |
| src/test/scala/tests/test54_time/spec3.qtl | src/test/scala/tests/test54_time/log1.timed.csv | 9 | 2 | 2 | MATCH |
| src/test/scala/tests/test54_time/spec4.qtl | src/test/scala/tests/test54_time/log1.timed.csv | 9 | 3 | 3 | MATCH |
| src/test/scala/tests/test55_time/spec1.qtl | src/test/scala/tests/test55_time/log1.timed.csv | 12 | 2 | 2 | MATCH |
| src/test/scala/tests/test56_time/spec1.qtl | src/test/scala/tests/test56_time/log1.timed.csv | 1000 | 0 | 0 | MATCH |
| src/test/scala/tests/test57_synthesis_time/spec.qtl | src/test/scala/tests/test57_synthesis_time/spec.csv | 4 | 0 | 0 | MATCH |
| src/test/scala/tests/test6/spec.qtl | src/test/scala/tests/test6/log1.csv | 7 | 0 | 0 | MATCH |
| src/test/scala/tests/test6/spec.qtl | src/test/scala/tests/test6/log2.csv | 8 | 0 | 0 | MATCH |
| src/test/scala/tests/test6/spec.qtl | src/test/scala/tests/test6/log3.csv | 8 | 1 | 1 | MATCH |
| src/test/scala/tests/test7/spec.qtl | src/test/scala/tests/test7/log1.csv | 9 | 2 | 2 | MATCH |
| src/test/scala/tests/test7/spec.qtl | src/test/scala/tests/test7/log2.csv | 7 | 0 | 0 | MATCH |
| src/test/scala/tests/test8/spec.qtl | src/test/scala/tests/test8/log1.csv | 6 | 0 | 0 | MATCH |
| src/test/scala/tests/test8/spec.qtl | src/test/scala/tests/test8/log2.csv | 7 | 1 | 1 | MATCH |
| src/test/scala/tests/test8/spec.qtl | src/test/scala/tests/test8/log3.csv | 8 | 2 | 2 | MATCH |
| src/test/scala/tests/test9/spec.qtl | src/test/scala/tests/test9/log2.csv | 1 | 1 | 1 | MATCH |
| src/test/scala/tests/test9/spec.qtl | src/test/scala/tests/test9/log3.csv | 2 | 2 | 2 | MATCH |
| src/test/scala/tests/test9/spec.qtl | src/test/scala/tests/test9/log4.csv | 3 | 3 | 3 | MATCH |
