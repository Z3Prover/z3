# Performance Report: theory_nseq vs theory_seq vs ZIPT

## Results Table

| # | Benchmark | seq | t(s) | nseq | t(s) | zipt | t(s) | Notes |
|---|-----------|-----|------|------|------|------|------|-------|
| 1 | 20230329-automatark-lu/instance00000.smt2 | sat | 0.492 | timeout | 10.099 | sat | 0.460 | nseq<seq nseq<zipt |
| 2 | 20230329-automatark-lu/instance05331.smt2 | sat | 0.469 | timeout | 10.083 | sat | 0.496 | nseq<seq nseq<zipt |
| 3 | 20230329-automatark-lu/instance10662.smt2 | unsat | 0.511 | timeout | 10.087 | unsat | 0.489 | nseq<seq nseq<zipt |
| 4 | 20240318-omark/cloud-service-query-1.smt2 | sat | 7.603 | sat | 0.530 | sat | 1.092 |  |
| 5 | 20240318-omark/lyndon-schuetzenberg-3.smt2 | timeout | 10.065 | timeout | 10.490 | timeout | 10.410 |  |
| 6 | 20240318-omark/noodles-unsat-5.smt2 | timeout | 10.445 | unknown | 0.436 | sat | 0.939 | nseq<zipt |
| 7 | 20250410-matching/sub-matching-sat-1.smt2 | timeout | 10.074 | timeout | 10.448 | crash | 0.781 |  |
| 8 | 20250410-matching/sub-matching-unsat-16.smt2 | timeout | 10.472 | timeout | 10.443 | crash | 0.808 |  |
| 9 | 20250410-matching/wildcard-matching-regex-104.smt2 | sat | 0.531 | unknown | 0.085 | unknown | 0.404 | nseq<seq |
| 10 | 20250410-matching/wildcard-matching-regex-41.smt2 | crash | 0.389 | unknown | 0.341 | crash | 0.699 |  |
| 11 | 20250411-hornstr-equiv/Burns_lstar_non_incre_equiv_bad_0_0.smt2 | sat | 0.123 | unknown | 0.093 | sat | 0.503 | nseq<seq nseq<zipt |
| 12 | 20250411-hornstr-equiv/dining-cryptographers_sat_non_incre_equiv_init_0_3.smt2 | sat | 0.100 | unsat | 0.107 | sat | 0.488 | **BUG?** |
| 13 | 20250411-hornstr-equiv/muzzle_sat_non_incre_equiv_bad_0_13.smt2 | unsat | 0.059 | unsat | 0.097 | unsat | 0.419 |  |
| 14 | 20250411-negated-predicates/diseq-1-3-5-0.smt2 | timeout | 10.067 | sat | 0.461 | timeout | 10.000 | **nseq>seq** **nseq>zipt** |
| 15 | 20250411-negated-predicates/diseq-None-4-5-107.smt2 | timeout | 10.411 | sat | 0.437 | timeout | 10.000 | **nseq>seq** **nseq>zipt** |
| 16 | 20250411-negated-predicates/not-contains-1-4-5-112.smt2 | timeout | 10.445 | unknown | 0.430 | sat | 0.404 | nseq<zipt |
| 17 | pcp-3-3-random/pcp_instance_0.smt2 | unknown | 0.098 | timeout | 10.077 | unknown | 0.321 |  |
| 18 | pcp-3-3-random/pcp_instance_248.smt2 | unknown | 0.462 | timeout | 10.077 | unknown | 0.289 |  |
| 19 | pcp-3-3-random/pcp_instance_398.smt2 | unknown | 0.456 | timeout | 10.074 | unknown | 0.316 |  |
| 20 | pcp-3-4-hard/unsolved_pcp_instance_0.smt2 | unknown | 0.467 | timeout | 10.074 | unknown | 0.335 |  |
| 21 | pcp-3-4-hard/unsolved_pcp_instance_248.smt2 | unknown | 0.458 | timeout | 10.061 | unknown | 0.316 |  |
| 22 | pcp-3-4-hard/unsolved_pcp_instance_398.smt2 | unknown | 0.468 | timeout | 10.072 | unknown | 0.305 |  |
| 23 | queries/query2885.smt2 | sat | 0.886 | unknown | 0.093 | sat | 0.386 | nseq<seq nseq<zipt |
| 24 | queries/query3358.smt2 | sat | 0.519 | unknown | 0.068 | sat | 0.448 | nseq<seq nseq<zipt |
| 25 | queries/query3664.smt2 | sat | 0.271 | unknown | 0.072 | sat | 0.424 | nseq<seq nseq<zipt |
| 26 | queries/query6481.smt2 | sat | 0.218 | unknown | 0.069 | sat | 0.433 | nseq<seq nseq<zipt |
| 27 | queries-no-ree/query10041.smt2 | sat | 0.798 | unknown | 0.075 | sat | 0.448 | nseq<seq nseq<zipt |
| 28 | queries-no-ree/query3231.smt2 | sat | 0.444 | unknown | 0.474 | sat | 0.422 | nseq<seq nseq<zipt |
| 29 | queries-no-ree/query3723.smt2 | sat | 0.422 | unknown | 0.082 | sat | 0.451 | nseq<seq nseq<zipt |
| 30 | queries-no-ree/query5519.smt2 | sat | 0.222 | unknown | 0.090 | sat | 0.418 | nseq<seq nseq<zipt |
| 31 | rna-sat/benchmark_0001.smt2 | unknown | 0.079 | unknown | 0.060 | unknown | 0.275 |  |
| 32 | rna-sat/benchmark_0167.smt2 | unknown | 0.074 | unknown | 0.080 | unknown | 0.276 |  |
| 33 | rna-sat/benchmark_0333.smt2 | unknown | 0.109 | unknown | 0.090 | unknown | 0.269 |  |
| 34 | rna-unsat/benchmark_0001.smt2 | unknown | 0.080 | unknown | 0.097 | unknown | 0.246 |  |
| 35 | rna-unsat/benchmark_0167.smt2 | unknown | 0.091 | unknown | 0.088 | unknown | 0.269 |  |
| 36 | rna-unsat/benchmark_0333.smt2 | unknown | 0.099 | unknown | 0.094 | unknown | 0.293 |  |
| 37 | slog/slog_stranger_1001_sink.smt2 | unsat | 0.092 | unsat | 0.084 | unsat | 0.416 |  |
| 38 | slog/slog_stranger_2251_sink.smt2 | unsat | 0.433 | unsat | 0.077 | unsat | 0.352 |  |
| 39 | slog/slog_stranger_3947_sink.smt2 | sat | 0.218 | unknown | 0.094 | sat | 0.575 | nseq<seq nseq<zipt |
| 40 | track01/01_track_1.smt2 | sat | 0.084 | sat | 0.082 | sat | 0.404 |  |
| 41 | track01/01_track_144.smt2 | sat | 0.060 | sat | 0.094 | sat | 0.503 |  |
| 42 | track01/01_track_19.smt2 | sat | 0.073 | sat | 0.061 | sat | 0.434 |  |
| 43 | track01/01_track_54.smt2 | sat | 0.101 | sat | 0.093 | sat | 1.142 |  |
| 44 | track02/02_track_1.smt2 | timeout | 10.075 | sat | 0.523 | sat | 0.594 | **nseq>seq** |
| 45 | track02/02_track_4.smt2 | timeout | 10.072 | sat | 0.723 | sat | 6.008 | **nseq>seq** |
| 46 | track02/02_track_7.smt2 | timeout | 10.428 | sat | 0.644 | sat | 2.855 | **nseq>seq** |
| 47 | track03/03_track_1.smt2 | unsat | 0.065 | unsat | 0.080 | unsat | 0.472 |  |
| 48 | track03/03_track_144.smt2 | sat | 0.086 | sat | 0.075 | sat | 0.832 |  |
| 49 | track03/03_track_19.smt2 | unsat | 0.094 | unsat | 0.077 | unsat | 0.388 |  |
| 50 | track03/03_track_54.smt2 | timeout | 10.448 | unsat | 0.482 | unsat | 0.508 | **nseq>seq** |
| 51 | track04/04_track_1.smt2 | sat | 0.067 | sat | 0.062 | sat | 0.367 |  |
| 52 | track04/04_track_144.smt2 | unsat | 0.088 | unsat | 0.072 | unsat | 0.515 |  |
| 53 | track04/04_track_19.smt2 | unsat | 0.084 | unsat | 0.068 | unsat | 0.467 |  |
| 54 | track04/04_track_54.smt2 | sat | 0.085 | sat | 0.084 | sat | 0.462 |  |

## Summary Statistics

- **Benchmarks solved (sat/unsat)**: seq=30, nseq=22, zipt=35 (out of 54)
- **Total solve time (solved only)**: seq=15.3s, nseq=5.0s, zipt=26.0s
- **nseq wins vs seq**: 6 benchmarks solved by nseq but not seq
- **nseq wins vs zipt**: 2 benchmarks solved by nseq but not zipt
- **nseq loses vs seq**: 14 benchmarks solved by seq but not nseq
- **nseq loses vs zipt**: 15 benchmarks solved by zipt but not nseq

## Potential Soundness Issues

- **#12 20250411-hornstr-equiv/dining-cryptographers_sat_non_incre_equiv_init_0_3.smt2**: seq=sat, nseq=unsat, zipt=sat

## Worst nseq Regressions

Benchmarks where nseq is worse than both seq and zipt:

1. **20230329-automatark-lu/instance00000.smt2** — seq=sat(0.492s), nseq=timeout(10.099s), zipt=sat(0.46s)
2. **20230329-automatark-lu/instance05331.smt2** — seq=sat(0.469s), nseq=timeout(10.083s), zipt=sat(0.496s)
3. **20230329-automatark-lu/instance10662.smt2** — seq=unsat(0.511s), nseq=timeout(10.087s), zipt=unsat(0.489s)
4. **queries-no-ree/query3231.smt2** — seq=sat(0.444s), nseq=unknown(0.474s), zipt=sat(0.422s)
5. **20250411-hornstr-equiv/Burns_lstar_non_incre_equiv_bad_0_0.smt2** — seq=sat(0.123s), nseq=unknown(0.093s), zipt=sat(0.503s)
6. **slog/slog_stranger_3947_sink.smt2** — seq=sat(0.218s), nseq=unknown(0.094s), zipt=sat(0.575s)
7. **queries-no-ree/query5519.smt2** — seq=sat(0.222s), nseq=unknown(0.09s), zipt=sat(0.418s)
8. **queries/query6481.smt2** — seq=sat(0.218s), nseq=unknown(0.069s), zipt=sat(0.433s)
9. **queries/query3664.smt2** — seq=sat(0.271s), nseq=unknown(0.072s), zipt=sat(0.424s)
10. **queries/query2885.smt2** — seq=sat(0.886s), nseq=unknown(0.093s), zipt=sat(0.386s)

## nseq Strengths (where nseq beats seq or zipt)

- **20250411-negated-predicates/diseq-1-3-5-0.smt2**: seq=timeout(10.067s), nseq=sat(0.461s), zipt=timeout(10.0s)
- **20250411-negated-predicates/diseq-None-4-5-107.smt2**: seq=timeout(10.411s), nseq=sat(0.437s), zipt=timeout(10.0s)
- **track02/02_track_1.smt2**: seq=timeout(10.075s), nseq=sat(0.523s), zipt=sat(0.594s)
- **track02/02_track_4.smt2**: seq=timeout(10.072s), nseq=sat(0.723s), zipt=sat(6.008s)
- **track02/02_track_7.smt2**: seq=timeout(10.428s), nseq=sat(0.644s), zipt=sat(2.855s)
- **track03/03_track_54.smt2**: seq=timeout(10.448s), nseq=unsat(0.482s), zipt=unsat(0.508s)