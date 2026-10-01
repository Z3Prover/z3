# QF_SLIA Performance: `c3mv` versus `master`

Benchmark comparison:

<https://z3prover.github.io/coz3/compare_stats.html?a=run-1166-qf-slia-c3mv-20260930-stats.md&b=run-0907-qf-slia-master-stats.md>

## Executive summary

The primary weakness in `c3mv` is satisfiable-instance coverage and model
construction, not general execution speed.

Across 84,411 matched benchmarks, `c3mv` solves 50,917 instances versus
73,682 for `master`, a net loss of 22,765. This occurs even though the
`c3mv` run used a 10-second timeout while the `master` run used a 5-second
timeout.

On the 47,178 instances solved by both versions, however, `c3mv` is about
10.5% faster by geometric mean and uses approximately the same amount of
memory. Therefore, broad low-level optimization is not the first priority.
The largest gains should come from restoring SAT search completeness,
producing models earlier, and avoiding premature `unknown`.

## Important comparison caveat

The two experiments did not use equivalent options:

| Run | Commit | Options |
|---|---|---|
| `c3mv` | `c2e50836d5a123e70ab049856cf883d9bae5ce0d` | `-T:10 model_validate=true` |
| `master` | `079eb4b53405f3e3d4dd58aad4cf15d4d1f9860d` | `-T:5` |

Both versions should be rerun with the same timeout and with
`model_validate=true`. Nevertheless, the coverage regression is robust:
`c3mv` receives twice as much time and still produces about three times as
many timeouts.

## Aggregate results

| Result | `master` | `c3mv` |
|---|---:|---:|
| SAT | 41,962 | 18,601 |
| UNSAT | 31,720 | 32,316 |
| Timeout | 10,547 | 30,057 |
| Unknown | 182 | 3,199 |
| Error | 0 | 238 |
| Solved | 73,682 | 50,917 |

The most important status transitions are:

| `master` to `c3mv` | Count |
|---|---:|
| SAT to timeout | 22,098 |
| SAT to unknown | 2,679 |
| UNSAT to timeout | 1,273 |
| UNSAT to unknown | 265 |
| SAT to error | 122 |
| Timeout to SAT | 2,275 |
| Timeout to UNSAT | 1,422 |
| SAT to UNSAT | 779 |

All 30,057 `c3mv` timeouts run to the configured limit: the median reported
time is 10.046 seconds. They are not short cancellations or reporting
artifacts.

## Main improvement areas

### 1. Recover satisfiable word-equation coverage

This is the highest-impact performance area. `c3mv` loses 22,098 instances
that `master` solves as SAT to timeout, plus another 2,679 that become
unknown.

The Reynolds benchmark collection accounts for 22,752 of the total 22,765
net lost solves:

| Family | `master` solved | `c3mv` solved | Net |
|---|---:|---:|---:|
| Reynolds PyEx | 20,460 | 2,610 | -17,850 |
| Reynolds Kaluza | 18,997 | 14,095 | -4,902 |

The largest concentration is PyEx `httplib2`:

| Family | Net solved loss |
|---|---:|
| `peterc-pyex-doc-cav17-zz/httplib2` | -9,097 |
| `peterc-pyex-doc-cav17-z3/httplib2` | -4,551 |
| `peterc-pyex-doc-cav17-td/httplib2` | -3,441 |

Kaluza also shows a strong SAT-specific regression:

| Family | Net solved loss |
|---|---:|
| `kaluza/sat/small` | -3,359 |
| `kaluza/sat/big` | -403 |

These benchmarks are dominated by satisfiable concatenation and word-equation
constraints. The likely improvement areas are:

- select variable assignments and Nielsen substitutions that lead to small
  models;
- propagate exact and bounded lengths into substitution choices;
- detect a complete SAT leaf sooner instead of continuing refutation-oriented
  splitting;
- construct witnesses incrementally as equations are eliminated;
- prioritize branches compatible with the arithmetic model;
- avoid repeating equivalent word-equation states.

The data suggests that `c3mv` often traverses solved branches efficiently but
has difficulty finding the satisfying branch.

### 2. Diagnose and eliminate premature `unknown`

Unknown results increase from 182 to 3,199.

The search tree now preserves the distinction between:

- `depth_cutoff`, where the configured search-depth budget truncated at least
  one subtree;
- `unknown`, where propagation reached an unsatisfied leaf and no split plugin
  could reduce it.

The statistics now report `seq-stx num depth cutoff` separately from
`seq-stx num unknown`. Further diagnostics should distinguish:

- depth cutoff;
- unsupported operation;
- exhausted split iterator;
- monadic budget, state cap, state expansion, or resource exhaustion;
- unresolved equation, disequation, membership, power, or higher-order term;
- failure to materialize a witness;
- absence of an applicable split despite an unsatisfied facet.

For every give-up, the statistics should identify the final active facet,
search depth, nodes explored, pending equations, pending memberships, and
monadic bail reason.

Where nseq encounters an unsupported state, falling back to the legacy `seq`
solver would be more useful than immediately returning unknown. This is
especially relevant because nseq is the default string solver on `c3mv`:

- `src/params/smt_params_helper.hpp:158`

### 3. Fix model-validation and result discrepancies

The `c3mv` run reports 238 invalid models because it enables
`model_validate=true`. At least 86 of these occur in transformed z3str2
benchmarks:

- 59 were SAT on `master`;
- 27 timed out on `master`.

There are also 779 cases that are SAT on `master` and UNSAT on `c3mv`. They
are concentrated in string/integer workloads:

| Family | SAT to UNSAT |
|---|---:|
| `restoreIpAddresses` cvc4 | 228 |
| `validWordAbbreviation` z3seq | 90 |
| `restoreIpAddresses` z3seq | 70 |
| IP-address parsing variants | 199 |
| `numDecodings` variants | 88 |

These transitions are an unsoundness bug in `c3mv`. A representative
`restoreIpAddresses` case reduces to:

```smt2
(declare-const s String)
(assert (= (str.to_int (str.at s 0)) 0))
(check-sat)
```

The legacy `seq` solver returns SAT with `s = "0"`, while nseq returns UNSAT.
The reproducer is saved as `str-at-unsound.smt2`.

The final false conflict excludes the conjunction of:

- `s = unit(nth_i(s, 0)) ++ tail(s, 0)`;
- `unit(nth_i(s, 0)) = str.at(s, 0)`;
- `str.at(s, 0)` is in `[0-9]+`.

All three constraints hold for `s = "0"`, so the generated theory conflict
is invalid.

The exact failing path is:

1. `nielsen-split` takes its `v:=c.v'` edge twice, leaving the membership
   `unit(nth_i(s,0)) in [0-9]+`.
2. `mem-propagate` computes the derivative of `[0-9]+` with respect to the
   symbolic character `nth_i(s,0)` into the local expression `cur`.
3. Nullability of `cur` is undecided, so propagation continues.
4. The `rejects-view` check calls `seq::accepts(sm.m_view, m_rw)` on the
   original `[0-9]+` view instead of checking `cur`.
5. Since `[0-9]+` itself is non-nullable, `accepts` returns false and the
   satisfiable branch is incorrectly closed.

The root cause is therefore the stale-view acceptance check in
`mem_propagation::propagate`, not missing `str.at` axioms or compound-term
substitution. Propagating the derivative's nullability condition removes the
false UNSAT. Disequality propagation can then use `seq_rewriter` to discharge
constraints whose corresponding equation is inconsistent. The minimal
reproducer reaches SAT search, but model validation still rejects the generated
model; the two sampled `restoreIpAddresses` cases time out rather than returning
false UNSAT.

### 4. Improve string/integer and higher-order operation integration

The `2019-full_str_int` suite loses 468 net solves. Important focused losses
include:

| Family | Lost solves |
|---|---:|
| trauc `addStrings` | 440 |
| cvc4 `addStrings` | 305 |
| cvc4 `add_binary` | 208 |
| z3seq `add_binary` | 150 |

Other relevant regressions include:

- `str-rep-all`: 145 solved on `master`, 22 on `c3mv`;
- transformed stringfuzz/z3str2: 7,431 solved on `master`, 6,367 on `c3mv`;
- `20250410-matching`: 1.65 times slower on the six instances solved by both;
- several solved `restoreIpAddresses` examples are 20 to 40 times slower.

This points to incomplete or poorly scheduled interaction among:

- word equations;
- length arithmetic;
- `str.to_int` and `int.to_str`;
- replace and replace-all axioms;
- arithmetic-model extraction;
- final string-model construction.

The recent incremental forwarding of length bounds is useful, but the
benchmark results indicate that these bounds are not yet being exploited
effectively enough during SAT branch selection and witness construction.

### 5. Tune monadic checks selectively

The monadic and regex work should not be disabled globally. It is one of
`c3mv`'s strengths:

- generated stringfuzz gains 1,037 net solves;
- the geometric mean on instances solved by both versions is 0.895;
- total time on both-solved instances drops from 20,683 to 18,124 seconds.

The problem appears to be the interaction between monadic checks and mixed
word-equation/SLIA problems.

Current relevant defaults are:

| Parameter | Default |
|---|---:|
| `smt.seq.monadic_leaf` | `true` |
| `smt.seq.monadic_leaf_budget` | `300000` |
| `smt.seq.monadic_leaf_root` | `true` |
| `smt.seq.monadic_leaf_budget_root` | `50000` |
| `smt.seq.regex_precheck` | `true` |
| `smt.seq.mem_monadic_endgame` | `false` |

Definitions:

- `src/params/smt_params_helper.hpp:168-173`

Uses:

- `src/ast/seq/seq_mem_facet.cpp:314`
- `src/ast/seq/seq_mem_facet.cpp:432`
- `src/ast/seq/seq_mem_facet.cpp:983-998`

The root monadic ask is refutation-only while equations are still pending.
This can be valuable for pure regex problems but may consume a substantial
budget without helping model discovery on large satisfiable equation systems.

An adaptive policy should use strong monadic checks on regex-dominant
instances while reducing or postponing them when:

- many word equations remain;
- the instance is dominated by concatenation;
- the monadic call repeatedly returns undefined;
- the previous calls did not refute or commit a witness;
- string/integer terms still determine the required lengths.

## Recommended A/B experiments

Use identical options for all runs:

```text
-T:10 model_validate=true
```

Evaluate the following c3mv configurations:

```text
baseline
smt.seq.monadic_leaf_root=false
smt.seq.monadic_leaf=false
smt.seq.regex_precheck=false
smt.seq.mem_monadic_endgame=true
```

Use stratified samples from:

1. PyEx `httplib2`;
2. Kaluza SAT small and big;
3. `addStrings` and `add_binary`;
4. transformed stringfuzz/z3str2;
5. generated regex stringfuzz;
6. `str-rep-all`;
7. matching benchmarks.

Collect `-st` statistics and, for the unknown subset, diagnostics equivalent
to `NSEQ_DUMP_UNKNOWN=1`.

The most useful metrics are:

- solved count by SAT and UNSAT;
- SAT-to-timeout and SAT-to-unknown transitions;
- search-tree nodes and maximum depth;
- counts per split and propagation plugin;
- monadic calls, cache hits, refutations, committed witnesses, and bail
  reasons;
- number of final checks;
- number of branches rejected by arithmetic assumptions;
- time to first candidate SAT leaf;
- time spent constructing and validating the model.

## Recommended implementation order

1. Rerun `master` and `c3mv` with identical timeout and validation options.
2. Fix invalid models and classify SAT/UNSAT disagreements.
3. Add structured unknown/depth-cutoff statistics.
4. Profile representative PyEx and Kaluza SAT timeouts.
5. Improve SAT branch ordering and incremental witness construction.
6. Tune root/per-node monadic checks using the targeted A/B matrix.
7. Address string/integer and replace-all integration.

The central goal should be to retain c3mv's speed on solved and regex-heavy
instances while recovering the approximately 22,000 satisfiable instances
that currently time out.
