# QF_SLIA Performance: `c3mv` versus `master`

## Latest directly comparable update: run 1174 versus run 1173

The newest directly comparable QF_SLIA reports are:

| Branch | Report | Commit | Date | Options |
|---|---|---|---|---|
| `c3mv` | `run-1174-qf-slia-c3mv-stats.md` | `34125a907` | 2026-10-13 21:51 UTC | `-T:5 model_validate=true` |
| `master` | `run-1173-qf-slia-master-stats.md` | `570f56aaa` | 2026-10-13 19:39 UTC | `-T:5 model_validate=true` |

Both reports cover the same 84,411 inputs. Unlike the earlier comparison
below, timeout and model-validation settings are identical.

| Result | `master` | `c3mv` | Difference |
|---|---:|---:|---:|
| SAT | 44,013 | 23,413 | -20,600 |
| UNSAT | 32,263 | 31,922 | -341 |
| Timeout | 7,955 | 23,925 | +15,970 |
| Unknown | 180 | 4,854 | +4,674 |
| Error | 0 | 297 | +297 |
| Solved | 76,276 | 55,335 | -20,941 |

The dominant transitions are:

| `master` to `c3mv` | Count |
|---|---:|
| SAT to timeout | 17,027 |
| SAT to unknown | 4,289 |
| UNSAT to timeout | 500 |
| UNSAT to unknown | 316 |
| SAT to invalid model | 248 |
| Timeout to SAT | 923 |
| Timeout to UNSAT | 475 |

On the 53,896 instances solved by both, `c3mv` is now 6.85% slower by
geometric mean, with a median ratio of 1.057. Total time rises from 21,606
seconds to 23,141 seconds. Memory is effectively unchanged: the geometric
mean ratio is 0.984 and the median ratio is 1.005.

### Latest bottleneck ranking

#### 1. PyEx `httplib2`: exponential equation/disequality search

Reynolds PyEx remains by far the largest coverage loss:

| Family | `master` solved | `c3mv` solved | Net |
|---|---:|---:|---:|
| `zz/httplib2` | 9,649 | 1,406 | -8,243 |
| `z3/httplib2` | 5,178 | 670 | -4,508 |
| `td/httplib2` | 4,194 | 793 | -3,401 |
| all PyEx | 20,821 | 3,892 | -16,929 |

These are mostly easy SAT instances for `master`: 17,027 master-SAT inputs
time out in `c3mv`. A representative `httplib2-entry-disposition` instance
reaches the five-second limit with:

```text
4,106 DFS nodes
870 Nielsen splits
192 disequality splits
2,819 equation-propagation progress steps
maximum search depth 97
445 constraints retained in the search store
```

The formula repeatedly applies `contains`, `substr`, and `str.at` to the same
prefix of one string. The current encoding turns these correlated tests into
many independent equation and disequality choices. The first improvement
target should be sharing/canonicalizing repeated substring and character
decompositions, followed by stronger subsumption or caching of equivalent
equation states. Branch ordering alone is unlikely to recover 16,929 solves
without reducing the state space.

##### `httplib2` proof and model deep dive

Running both solvers from the same `c3mv` executable isolates the algorithmic
gap:

| Representative | legacy `seq` | `nseq` before direct inference |
|---|---:|---:|
| master-easy SAT | SAT in about 0.02s | unknown in 7.93s |
| master-easy UNSAT | UNSAT in about 0.09s | UNSAT in 2.32s |

The SAT instance has a tiny model:

```smt2
value2 = "F\u{9}"
key2 = "cache-control"
```

There is no SAT proof in the refutation sense; the evidence is this witness.
The constraints require `value2` to contain `F`, end in TAB, avoid the other
tested characters, comma, and `"="`, and be nonempty. `"F<TAB>"` is the
minimal witness.

The UNSAT instance has a small decisive proof core. Let:

```smt2
i = str.indexof(value1, "=", 0)
p = str.substr(value1, 0, i)
q = str.substr(p, 0, str.len(p) - 1)
```

The input implies:

```smt2
i >= 0
str.len(q) > 0
str.at(q, 0) = CR
str.at(p, 0) != CR
```

Because nonempty `q` is `p` with only its last character removed,
`str.at(q,0) = str.at(p,0)`, yielding the contradiction. Legacy `seq`
produces a 34 KB proof whose final conflict is exactly the equality and
disequality of this first character.

This proof can be simulated by `nseq`. The reduced proof core is solved in
about 0.02 seconds, and proof-enabled `nseq` emits a 4.8 KB proof using the
same sequence decomposition, `str.at`, and length lemmas. The gap is
therefore proof discovery, not missing proof expressiveness.

Two concrete discovery/completion problems were identified:

1. The shared indexof axiom creates a guarded internal equation:

   ```text
   value2 = idx.l(value2,"=") ++ "=" ++ idx.r(value2,"=")
   ```

   Internal `seq.eq` atoms are phase-selected true. Even when
   `indexof(value2,"=",0) = -1` and `not contains(value2,"=")`, SAT may first
   assign this irrelevant guarded equation true. Legacy `seq` rejects it
   cheaply. `nseq` previously sent it through thousands of Nielsen steps.

2. After the guarded equation is rejected, the SAT leaf still contains
   self-decompositions such as:

   ```text
   value2 = unit(nth_i(value2,0)) ++ tail(value2,0)
   value2 = unit(nth_i(value2,0)) ++ unit(nth_i(value2,1))
            ++ tail(value2,1)
   ```

   With `str.len(value2) = 2`, arithmetic already fixes
   `nth_i(value2,0) = 'F'`, `nth_i(value2,1) = TAB`, and the final tail
   length to zero. Nevertheless, `nseq` returns unknown because it requires
   every residual equation and negative-containment obligation to be
   syntactically discharged. Adding the explicit witness
   `value2 = "F\u{9}"` returns SAT immediately.

A dependency-preserving cross-facet rule was added for the first problem:
`not contains(H,N)` conflicts immediately with an active equation
`H = U ++ N ++ V`, including cyclic indexof-skolem equations that cannot be
handled by ordinary variable substitution. On the representative SAT case
this reduces:

```text
Nielsen splits: 1,212 -> 282
DFS nodes:       5,769 -> 3,904
time:            7.93s -> 2.47s
```

It does not by itself recover SAT. In a sample of 12 master-easy SAT cases,
several five-second timeouts became 2-3 second unknowns, but none reached a
complete model.

A first model-guided split prototype read sequence lengths and `nth_i`
values, guessed a concrete string, and used `s != candidate` as an exhaustive
fallback. It did not close the representative and caused search regressions,
so candidate enumeration was removed.

The replacement is a terminal model-completion step that runs only after
ordinary propagation and splitting are exhausted. It assigns finite-valued
sequence tokens their leaf-model values, records each sequence equality in
the assumption facet, and substitutes the values through every facet. If the
candidate closes the leaf, the search returns SAT and `theory_nseq` promotes
the equalities to SMT assumptions before accepting the model. If completion
fails, a branch-local fallback preserves `unknown` rather than deriving
UNSAT.

On the representative, this recovers the expected witness
`value2 = "F\u{9}"` and changes the result from unknown in about 2.44s to
model-validated SAT in about 0.05s. The representative UNSAT case remains
UNSAT in about 2.29s. On the 12-case master-easy SAT sample, 10 cases now
return validated SAT in 0.05-0.17s; one remains unknown and one times out.

Further SAT-completion work should:

- diagnose the one remaining unknown and one timeout in the 12-case sample;
- extend completion beyond bounded strings when large or non-string
  sequences have compact model values;
- materialize values required by residual membership or lexicographic
  obligations, not only equation/disequality/negative-containment tokens;
- reduce repeated outer final checks when several model assumptions can be
  asserted together.

#### 2. Kaluza SAT unknowns: empty-sided disequality completion

Kaluza loses 1,688 net solves. The most actionable subset is 1,141
`kaluza/sat` instances that change from SAT to unknown. A representative
input reduces completely to:

```smt2
(declare-fun x () String)
(assert (not (= x "")))
(check-sat)
```

The final search state contains only:

```text
deq_facet:
  "" != x
```

`deq_facet::simplify` deliberately leaves this active, but
`deq_split::split` skips every disequality for which either side is empty.
The search therefore has no applicable split and returns a genuine unknown.

Root disequality notification now completes an empty-sided disequality with
a positive length constraint. For `"" != x`, it adds
`0 < str.len(x)` with the original dependency instead of retaining the
redundant disequality. There is no equal-length alternative because equal
length would make both sides empty and violate the disequality. The
representative now returns model-validated SAT immediately in one DFS node.

Disequalities that become empty-sided only after internal substitution still
need the same completion inside `deq_facet`; the current change addresses the
large root-level Kaluza pattern directly.

#### 3. `addStrings` and related SLIA: eager character bit-blasting

The largest full-string/integer losses include:

| Family | Net solved loss |
|---|---:|
| trauc `addStrings` | -439 |
| cvc4 `addStrings` | -301 |
| cvc4 `add_binary` | -208 |
| z3seq `add_binary` | -150 |

A representative trauc `addStrings` timeout does almost no nseq search. At
five seconds it has:

```text
1,844,501 Boolean variables
3,209,999 clauses
11,393 seq-char2bit conversions
about 1.21 GB peak memory
1 nseq final check
```

The formula repeatedly applies `str.at`, `str.substr`, and `str.to_int` to
single-character strings. The bottleneck is therefore eager or duplicated
character-bit encoding before productive word-equation search begins.
Priorities are:

- memoize generated `char.bit` atoms and their defining clauses;
- share repeated `nth_i`/digit constraints;
- avoid bit-blasting symbolic characters until a digit or range predicate
  requires it;
- delay full `str.to_int` expansion until lengths and Boolean branches make
  the term relevant.

#### 4. Transformed z3str2: repeated higher-order decompositions

Transformed z3str2 loses 910 net solves. A representative unknown reaches
maximum search depth 100 with five equations, four memberships, three
`str.to_int` terms, and 575 arithmetic/character constraints still active.
The state retains several overlapping decompositions:

```text
x = unit(nth_i(x,0)) ++ tail(x,0)
x = unit(nth_i(x,0)) ++ unit(nth_i(x,1)) ++ tail(x,1)
...
```

It performs 105 DFS nodes, eight Nielsen splits, and twelve monadic
membership splits before giving up. This is not primarily a regex issue.
Equivalent `str.at`/`tail` decompositions need to be shared or subsumed, and
the `str.at`/`str.to_int` encoding should avoid reintroducing progressively
longer prefixes of the same string as independent equations.

#### 5. Invalid models: search snapshot and outer arithmetic disagree

All 297 errors are invalid-model failures; 248 are SAT on `master`. They are
concentrated in Kaluza `unsat/big` and several Leetcode/string-integer
families.

In representative Kaluza input `15574.corecstrs.readable.smt2`, the selected
search snapshot constructs a 17-character value for `T4_13`, while the outer
model assigns its asserted length variable `I0_13` the value 7. The model
also assigns:

```text
T_SELECT_3 = true
PCTEMP_LHS_3 = 17
I0_13 = 7
PCTEMP_LHS_2 = 0
```

which falsifies the active branch equality
`PCTEMP_LHS_3 = I0_13 + PCTEMP_LHS_2`.

This indicates that model construction uses branch-local string equations
from the SAT snapshot without ensuring that all branch-local arithmetic
constraints are reflected in the outer SMT model. A SAT snapshot should not
be accepted until its arithmetic values agree with the outer model, or the
necessary arithmetic equalities/bounds should be propagated back before
model construction.

### Recommended implementation order from the latest run

1. Generalize empty-sided disequality completion after substitution and rerun
   the 1,141 Kaluza SAT-to-unknown cases.
2. Fix SAT-snapshot/outer-arithmetic model synchronization; invalid models
   make SAT coverage measurements unreliable.
3. Deduplicate and delay character-bit encoding for `str.at`/`str.to_int`.
4. Canonicalize repeated `substr`/`str.at`/`tail` decompositions.
5. Add equation-state subsumption and improve branch selection for PyEx
   `httplib2`.

## Earlier run-1166 analysis

Earlier benchmark comparison:

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

## Three-way QF_SLIA and regex follow-up

The comparable 10-second QF_SLIA runs are:

| Branch | Report | SAT | UNSAT | Timeout | Unknown | Errors |
|---|---|---:|---:|---:|---:|---:|
| `c3mv` | `run-1155` | 15,037 | 31,675 | 28,606 | 3,280 | 5,813 |
| `z3-tacas` | `run-1156` | 26,485 | 31,786 | 13,226 | 12,786 | 128 |
| `master` with `seq` | `run-1157` | 44,842 | 32,312 | 7,076 | 181 | 0 |

All three use `-T:10` and model validation. The main QF_SLIA deficit is SAT
coverage, not throughput on cases solved by both:

- versus `z3-tacas`, `c3mv` is about 5.4% faster geometrically on 43,697
  jointly solved instances, but loses 6,203 `z3-tacas` SAT results to timeout;
- versus `master`, `c3mv` is about 13.0% faster geometrically on 45,752
  jointly solved instances, but loses 22,392 master SAT results to timeout;
- Reynolds PyEx and Kaluza remain the dominant QF_SLIA coverage gaps.

The directly comparable regex runs are `run-1151` (`c3mv`) and `run-1152`
(`z3-tacas`), both over 2,711 inputs with a 10-second timeout:

| Branch | SAT | UNSAT | Timeout | Unknown |
|---|---:|---:|---:|---:|
| `c3mv` | 1,196 | 431 | 1,080 | 4 |
| `z3-tacas` | 1,195 | 1,165 | 351 | 0 |

Of these, 731 cases are `z3-tacas` UNSAT but `c3mv` timeout. They are
concentrated in ClemensRegex generated split-membership formulas. The master
regex report `run-1125` covers only 1,986 inputs, so only its 1,521 matched
rows should be compared; among those, 144 master UNSAT results become c3mv
timeouts.

### Implemented regex improvement

The generated split-membership formulas add definitional equations such as:

```text
x1 = sp1_a ++ sp1_b
x0 = sp2_a ++ sp2_b
```

The memberships alone can often be refuted quickly. Previously,
`eq_propagation` substituted these definitions before `mem_leaf_split` ran,
expanding two membership variables into four fresh variables and causing an
exponential monadic search.

`theory_nseq` now performs the existing dependency-tracked, refutation-only
monadic root check before equation propagation. When the check can consume
the root memberships, it replaces the first in-search root ask rather than
duplicating it. It is gated by the existing `seq.monadic_leaf` and
`seq.monadic_leaf_root` parameters.

On `split_membership_tiny_unsat_0003.smt2`:

| Configuration | Result | Median time | DFS nodes |
|---|---|---:|---:|
| root check disabled | UNSAT | about 4.5s | 50,796 |
| pre-propagation root check | UNSAT | about 0.05s | 0 |

On a sample of 12 cases that were `z3-tacas` UNSAT and old-c3mv timeout, the
new check solved 8 within 0.04-0.27 seconds under a 3-second limit. The four
remaining timeouts are length-heavy formulas whose refutations require
arithmetic integration rather than membership-only reasoning. A
representative generated SAT case remained at about 0.04 seconds.

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
