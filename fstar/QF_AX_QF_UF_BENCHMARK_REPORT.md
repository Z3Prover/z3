# QF_AX / QF_UF benchmark experiment: Z3 performance and rewrite-matcher coverage

This report documents a large-scale experiment driving the pure-F* Pulse-style
proof checker (`Z3PulseProofChecker.fst` + `Z3PatternMatchedProofChecker.fst`,
see [`PULSE_PROOF_CHECKER_REPORT.md`](PULSE_PROOF_CHECKER_REPORT.md)) against
**every `unsat`-annotated benchmark** in the official SMT-LIB 2025
non-incremental `QF_AX` and `QF_UF` logics, downloaded from the
[SMT-LIB Zenodo release](https://zenodo.org/records/16740866). It reports
(a) Z3's own solving performance with and without proof production, and
(b) how many of the proof's equational rewrite leaves were accepted as
instances of one of this project's verified rewrite-rule lemmas versus left
as unverified ("trusted") leftover obligations.

**Raw benchmark corpora, per-file results, and generated `.fst` files are not
committed to this repository** (they live under `C:\smtlib-benchmarks` on the
machine the experiment was run on, per instructions to keep downloaded
third-party corpora out of the repo). This document and the harness scripts
(`tools/run_benchmarks.py`, `tools/analyze_benchmarks.py`) are committed so the
experiment is reproducible.

## Methodology

For every benchmark file declaring `(set-info :status unsat)`:

1. **`z3_no_proof`**: fresh `z3.Solver()`, `timeout=10000`ms, proofs disabled
   — records `result` (`sat`/`unsat`/`unknown`) and wall-clock `time`.
2. **`z3_with_proof`**: fresh `z3.Solver()` with `proof=true`, same 10s
   timeout — if `unsat`, keeps the live solver to extract `.proof()`.
3. **Proof extraction**: if (2) produced a proof, `tools/extract_z3_proof.py`'s
   `Converter`/`find_equational_root` machinery (already used throughout this
   project) walks the proof DAG, converts every `PR_REWRITE`/`PR_MONOTONICITY`
   step into this project's `Z3ProofTheory` calculus, and classifies each
   `Rewrite s t` leaf via `classify_rewrite(s, t)` — the same 7-way matcher
   (`reflexivity`, `select_store_same`, `store_same_twice`, `store_redundant`,
   `concat_assoc`, `not_not`, `bvand_self`) wired into
   `Z3PatternMatchedProofChecker.fst`.
4. **`fstar_check`**: the extracted proof is rendered into a generated `.fst`
   module (same template as every other `Z3ExtractedProof*.fst` snapshot in
   this repo) and checked with `fstar.exe --include fstar --smt z3.exe`,
   **10s timeout**, classified `pass` (exit 0 and F* printed "All
   verification conditions discharged successfully"), `fail` (ran to
   completion but an assertion did not go through), or `timeout`.

All three phases were run with a strict **10-second timeout each**, as
specified. Runs used a `multiprocessing.Pool` harness (up to 28 of the
machine's 32 cores) since per-file cost is dominated by a fixed, largely
sequential `fstar.exe` start-up cost (see "Performance" below) rather than
by the size of the specific benchmark, making the workload embarrassingly
parallel.

## What a `pass` does and does not certify

The generated file's "pass" independently checks **two separate things**,
and it is important not to conflate them:

1. `check_extracted` runs the *real* `Z3PulseProofChecker.check_proof` over
   the whole extracted derivation and asserts it accepts (`ok == true`) —
   this validates that the proof's modus-ponens/congruence *composition* is
   well-formed per the kernel calculus.
2. `lemma_unmatched_count_cross_checked` independently recomputes
   `collect_unmatched` (the verified, `Z3PatternMatchedProofChecker.fst`
   function, not the Python mirror) and asserts its length equals the
   count recorded by the Python-side log.

Point (2) means a file can `pass` even when it has **unmatched leaves** —
those leaves remain a precisely-counted, named set of unverified ("trusted")
leaf facts, not silently accepted falsehoods. A benchmark is **fully
verified end-to-end** (every rewrite leaf proven true by a lemma, zero
trusted leftovers) only when `pass` *and* `unmatched_count == 0`. Both
counts are reported separately below. `fail` outcomes were inspected
directly (see below) and are SMT-budget (`z3rlimit`/`fuel`) exhaustion of
the cross-check recomputation for benchmarks with many leaves, not instances
of the kernel checker accepting something it shouldn't — `check_proof`
itself still only accepts well-formed compositions.

## QF_AX results (279 unsat benchmarks)

| Z3 phase | result |
|---|---|
| `z3_no_proof` | 279/279 `unsat` (mean 38ms, median 6ms, max 2.44s) |
| `z3_with_proof` | 279/279 `unsat` (mean 81ms, median 11ms, max 5.40s) |

Proof extraction succeeded for all 279 (array theory benchmarks are small).

| F* check (10s timeout) | count | % |
|---|---|---|
| `pass` | 197 | 70.6% |
| `timeout` | 72 | 25.8% |
| `fail` | 10 | 3.6% |

F* check wall-clock: mean 9.31s, median 9.10s, min 7.20s, max 10.12s — i.e.
**every single invocation**, pass or fail, took 7.2 - 10.1 seconds, confirming
the fixed per-invocation F* start-up cost (loading `.checked` interfaces for
the whole theory stack, spawning Z3 as the tactic solver) dominates, not
benchmark-specific proof complexity.

Rewrite leaves: **486 total**, **3 matched** (0.6%: 2 `store_redundant` + 1
`reflexivity`), **483 unmatched** (99.4%). Of the 197 `pass` files, only
**1** is fully verified (0 unmatched leaves); the rest `pass` the composition
+ cross-check but still carry unverified leaf obligations.

Outer-shape breakdown of the 483 unmatched leaves (`head(s) -> head(t)`):

| count | shape |
|---|---|
| 102 | `let ... -> let ...` (Z3's proof-printer `let`-abbreviations) |
| 79 | atom `-> store ...` |
| 74 | atom `-> let ...` |
| 70 | `select ... -> select ...` |
| 58 | atom `-> <nested>` |
| 48 | atom `-> atom` |
| 34 | `= ... -> = ...` (equality re-orientation) |
| rest | `not`, mixed `let`/`store`/`select` combinations |

These are overwhelmingly **array-extensionality and multi-step store/select
chains** (e.g. `(store (store (store S aaa vvv) a v) aa vv) ->
(store (store (store S a v) aa vv) aaa vvv)`, i.e. *store commutativity* —
`storecomm_*` is in fact the dominant benchmark family in QF_AX) plus
`array-ext` witness terms. **`store_commute` is not yet one of the seven
verified matchers** (it needs an explicit `i <> j` side condition, unlike the
six other array/bv/seq schemas, which is why it was intentionally left out
of the original matcher set); this experiment is the first concrete,
large-scale evidence of how much of real-world QF_AX proof content it would
cover if added.

## QF_UF results (4361 unsat benchmarks)

| Z3 phase | result |
|---|---|
| `z3_no_proof` | 4267 `unsat` / 94 `unknown` (timeout) — mean 605ms, median 31ms, max 10.03s |
| `z3_with_proof` | 4136 `unsat` / 225 `unknown` — mean 1.27s, median 71ms, max 10.63s |

Proof production itself measurably slows Z3 down on the harder end of this
set: 131 extra benchmarks flip from `unsat` (no proof) to `unknown` (with
proof, same 10s budget) purely due to proof-logging overhead. 3 further
files produced a proof Z3 accepted but from which no equational root could
be extracted (non-equational refutation shape). This leaves **4133** files
on which the F* check was attempted; **228** benchmarks got no F* attempt at
all (94 + 131 timed-out-before-a-usable-proof-existed + 3 extraction
failures).

| F* check (10s timeout, n=4133 attempted) | count | % |
|---|---|---|
| `pass` | 1704 | 41.2% |
| `timeout` | 2375 | 57.5% |
| `fail` | 54 | 1.3% |

F* check wall-clock (over attempted files): mean 9.71s, median 10.09s, min
8.19s, max 11.45s — again overwhelmingly clustered right at the 10s
boundary; QF_UF's typically larger proof DAGs (more leaves per benchmark,
see below) push a majority of files past the cap where QF_AX's smaller ones
mostly stayed under it.

Rewrite leaves: **7,818 total**, **2,760 matched** (35.3%: 2,721
`reflexivity` + 39 `not_not`), **5,058 unmatched** (64.7%). Of the 1,704
`pass` files, **684** are fully verified end-to-end (0 unmatched leaves).

Outer-shape breakdown of the 5,058 unmatched leaves:

| count | shape | likely source |
|---|---|---|
| 1,886 | `(op ...) -> atom` | uninterpreted-function congruence / simplification to a case-split value |
| 988 | `= -> =` | equality re-orientation / argument-order normalization |
| 784 | `atom -> (op ...)` | inverse direction of the above |
| 612 | `let -> let` | proof-printer `let`-abbreviation restructuring |
| 279 | `and -> let` | CNF/Tseitin restructuring introducing `let`-bound literals |
| 148 | `op -> op` | rewrites between two compound uninterpreted-function terms |
| 99 | `and -> not` / 71 `= -> not` | De Morgan / implication-to-disjunction normalization |
| 26-27 | `atom <-> ite` / named function symbols (`f1..f5`) | if-then-else and function-specific congruence instances |

Representative concrete examples pulled from the corpus:

```
(=> rd1 (not rd2))                    -> (or (not rd1) (not rd2))
(and i2 (or (not i1) p2))             -> (not (or (not i2) (not (or (not i1) p2))))
(or prt (not (or (not car) (not clk))))
                                       -> (or prt (not (or k!0 (not clk))))
(= (or k!4 k!3) org)                  -> (= (or k!3 k!4) org)
(ite y$i y$n1s8 y$n0s8)               -> y$state$next
(f5 c_0 c_2)                          -> c_1
```

None of these are array/bitvector/sequence rewrites (QF_UF has no arrays, no
bitvectors, no sequences by construction) — they are entirely **propositional
normalization (implication-elimination, De Morgan, CNF/Tseitin
`let`-flattening, commutative re-ordering) and EUF congruence-closure
facts** (uninterpreted function applications simplifying to the value forced
by a prior case split/unit-propagation). None of the seven currently-verified
matchers target this theory family at all — they were built for
array/bitvector/sequence/boolean-double-negation rewrites specifically. This
is the clearest finding of the QF_UF run: **to meaningfully raise QF_UF
coverage, the matcher library needs a family of propositional-normalization
and congruence-closure lemmas**, not more array/bv/seq matchers.

## Combined summary

| | QF_AX | QF_UF |
|---|---|---|
| unsat benchmarks | 279 | 4,361 |
| Z3 solved (no proof) | 279 (100%) | 4,267 (97.8%) |
| Z3 solved (with proof) | 279 (100%) | 4,136 (94.8%) |
| F* check attempted | 279 | 4,133 |
| F* `pass` | 197 (70.6%) | 1,704 (41.2%) |
| F* `timeout` | 72 (25.8%) | 2,375 (57.5%) |
| F* `fail` | 10 (3.6%) | 54 (1.3%) |
| rewrite leaves (total) | 486 | 7,818 |
| leaves matched by a verified lemma | 3 (0.6%) | 2,760 (35.3%) |
| fully-verified files (`pass` + 0 unmatched) | 1 | 684 |

## Honest performance finding

A single `fstar.exe` invocation on even the smallest generated proof file in
this experiment costs **7-10+ seconds**, dominated by loading this project's
`.checked` interfaces (`Z3AstTheory`, `Z3ProofTheory`,
`Z3InterpretedProofChecker`, `Z3PatternMatchedProofChecker`,
`Z3PulseProofChecker`, ...) and spawning Z3 as the tactic solver — this cost
is essentially *independent* of the specific benchmark's proof size. The
user-mandated 10-second proof-checking timeout is therefore a genuinely
tight constraint for this experiment: it is not benchmark-complexity-driven
timeouts that dominate the `timeout` counts above so much as this fixed
per-process start-up tax, which a batch/daemon-mode F* invocation (checking
many generated modules in one long-lived process) would eliminate. This
was confirmed by direct inspection of individual run times, which cluster
tightly in the 7-11s band regardless of a file's leaf/node count.

`fail` outcomes were individually inspected (e.g.
`swap_t1_np_sf_ai_00007_007`): F* completes within the time budget but one
of the two generated assertions — the `collect_unmatched`
length-cross-check, which forces F*'s SMT backend to unfold the matcher
recursion over every leaf — fails to discharge within the
`--z3rlimit 60 --fuel 4 --ifuel 4` budget used by the shared template
for benchmarks with several leaves. This is an SMT-resource-budget
artifact of the cross-check, **not** a case of the kernel proof checker
(`check_proof`/`checker_accepts`) accepting an ill-formed derivation.

## Reproducing

```powershell
# (benchmarks downloaded separately, outside this repo, to C:\smtlib-benchmarks)
python fstar\tools\run_benchmarks.py C:\smtlib-benchmarks\QF_AX --out qf_ax_results.jsonl --timeout 10 --workers 16
python fstar\tools\run_benchmarks.py C:\smtlib-benchmarks\QF_UF --out qf_uf_results.jsonl --timeout 10 --workers 28
python fstar\tools\analyze_benchmarks.py qf_ax_results.jsonl QF_AX
python fstar\tools\analyze_benchmarks.py qf_uf_results.jsonl QF_UF
```
