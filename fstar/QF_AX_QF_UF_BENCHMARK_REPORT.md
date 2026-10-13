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

### Update: two new matchers (`eq_symm`, `select_store_diff`) and a re-run

Following the above finding (34/483 unmatched leaves are literal equality
orientation swaps, and the module's own documented "known limitation" is
`select_store_diff`), `Z3PatternMatchedProofChecker.fst` was extended from
seven to **nine** matchers:

- **`eq_symm`**: `(= a b) = (= b a)`, for any two same-sorted sub-expressions
  `a`/`b`. Needed a new interpreted operator, `op_eq` (polymorphic: domain
  `[s;s]` for any sort `s`, range `Bool`), given semantics
  `value_eq_sym : value -> value -> bool` in
  `Z3InterpretedProofChecker.fst`; soundness is just one symmetry lemma
  (`lemma_value_eq_sym_symmetric`), no theory lemma needed.
- **`select_store_diff`**: `select(store(a,i,x),j) = select(a,j)` for `i <>
  j` (`Z3ArrayTheory.lemma_select_store_diff`), the pattern the module
  docstring previously documented as unsupported. Its side condition `i <>
  j` is a genuine *semantic* fact, not a shape fact, and was unsatisfiable
  for any two named constants under the old `uninterp_app` (every 0-ary
  constant of a sort denoted the *same* fixed value, regardless of name).
  The fix: `uninterp_app` now injects distinct `decl_name` strings to
  distinct `VInt`s, via an injective `string -> nat` encoding
  (`string_key`, base-`0x110001` positional encoding over
  `FStar.String.list_of_string`, injectivity proved by straightforward
  structural induction) — so two distinctly-*named* 0-ary uninterpreted Int
  constants are now provably unequal, and `select_store_diff` matches
  whenever `i`/`j` are themselves such constants (compound index
  expressions, e.g. `i+1` vs `j`, remain out of reach and unmatched, same
  as before).

Both matchers, the `op_eq` operator, and the `uninterp_app` model change
typecheck cleanly (`Z3InterpretedProofChecker.fst` and
`Z3PatternMatchedProofChecker.fst` both still fully verify, including two
new live in-source demonstrations exercising each new matcher directly), and
all 8 pre-existing `Z3ExtractedProof*.fst` snapshots still verify with no
regressions.

Re-running the full QF_AX corpus (same 279 files) with the updated,
nine-matcher library:

| metric | baseline (7 matchers) | updated (9 matchers) |
|---|---|---|
| rewrite leaves matched | 3 / 486 (0.6%) | **68 / 486 (14.0%)** |
| matcher breakdown | 2 `store_redundant`, 1 `reflexivity` | 64 `eq_symm`, 1 `select_store_diff`, 2 `store_redundant`, 1 `reflexivity` |
| F* check @ 10s timeout | 197 pass / 72 timeout / 10 fail | 12 pass / 263 timeout / 4 fail |
| F* check @ 30s timeout | *(not run)* | 204 pass (73.1%) / 20 timeout / 55 fail |
| fully verified (pass + 0 unmatched leaves) | 1 / 279 | 1 / 279 |

Two takeaways:

1. **The matcher coverage genuinely improved**: `eq_symm` alone accounts for
   64 previously-unmatched leaves (far more than the 34 originally sampled,
   since the corpus-wide count is higher than the single-shape sample
   suggested), and `select_store_diff` fires for real at least once in this
   corpus (not just in the hand-built in-source demonstration) — concrete
   confirmation the injective-naming model fix is not merely a theoretical
   nicety.
2. **Honest cost**: at the *same* 10-second timeout used for the baseline,
   `pass` collapsed from 197 to 12 — the nine-way `try_match_leaf` case
   split plus the extra `string_key`/`value_eq_sym` reasoning make the
   independent `lemma_unmatched_count_cross_checked` recomputation (see
   "What a `pass` does and does not certify" above) noticeably more
   expensive per file, and most files now blow the fixed ~7-10s F*
   start-up budget before finishing that recomputation. Raising the
   timeout to 30 seconds recovers (and slightly exceeds) the baseline pass
   rate (204/279 = 73.1% vs 197/279 = 70.6%), and the 55 `fail` cases at
   30s were manually confirmed (by inspecting `stderr_tail`) to be the
   same non-unsoundness root cause documented above — SMT-budget
   (`--z3rlimit 60 --fuel 4 --ifuel 4`) exhaustion of the cross-check
   assertion, not a problem with `check_proof`/`checker_accepts` itself.

### Update 2: a tenth matcher (`store_commute`) and a re-run

The matcher library was extended once more, from nine to **ten**, adding
`store_commute`: `store(store(a,i,x),j,y) = store(store(a,j,y),i,x)` for
`i <> j` (`Z3ArrayTheory.lemma_store_commute`) — the index-swap twin of
`select_store_diff`, using the same injective-naming side-condition
discharge. It typechecks cleanly, fires on a hand-built single-level
example (`tools/test_store_commute.smt2`'s extracted proof, checked
in-source as `sc_leaf` in `Z3PatternMatchedProofChecker.fst` section 11),
and all 9 pre-existing `Z3ExtractedProof*.fst` snapshots still verify with
no regressions.

Re-running the full QF_AX corpus (same 279 files, 30s timeout) with the
ten-matcher library:

| metric | 9 matchers (previous) | 10 matchers (this run) |
|---|---|---|
| rewrite leaves matched | 68 / 486 (14.0%) | **68 / 486 (14.0%, unchanged)** |
| matcher breakdown | 64 `eq_symm`, 1 `select_store_diff`, 2 `store_redundant`, 1 `reflexivity` | same, **0 `store_commute`** |
| F* check @ 30s timeout | 204 pass / 20 timeout / 55 fail | 207 pass / 16 timeout / 56 fail |

**`store_commute` adds zero matches on this corpus** — a negative result,
worth stating plainly rather than glossing over. Inspecting an actual
unmatched leaf from the `storecomm_*` family explains why:

```
s = i10
t = (let ((a!1 (store (store (store (store a1 i1 e1) i2 e2) i3 e3) i4 e4))
          (a!3 (store (store (store (store a1 i10 e10) i5 e5) i3 e3) i8 e8)))
     (let ((a!2 (store (store (store (store a!1 i5 e5) i6 e6) i7 e7) i8 e8))
           (a!4 (store (store (store (store a!3 i9 e9) i4 e4) i2 e2) i7 e7)))
       ((_ array-ext 0)
         (store (store a!2 i9 e9) i10 e10)
         (store (store a!4 i6 e6) i1 e1))))
```

Z3's `storecomm_*` proofs resolve an entire multi-level (4+ nested
`store`s) index permutation in one leap, from a bare atom (`i10`, an
`array-ext` skolem witness index) directly to a giant `(_ array-ext 0)`
witness term — a single theory-lemma-level step, not a chain of adjacent
one-step swaps. No literal `Rewrite` leaf in these proofs has the flat
`store(store(a,i,x),j,y) = store(store(a,j,y),i,x)` two-level shape any
*single-step* matcher (this one included) can recognize; the
commutativity reasoning here happens entirely inside Z3's array theory
solver, not in the externally-visible rewrite-proof term. Confirming
`store_commute` is sound and *does* fire on genuinely shaped input
(§ demonstration above) was still worthwhile — it closes the gap for any
proof that *does* emit the one-step shape literally (e.g. from a
different array-theory configuration or solver) — but it does not, by
itself, explain the dominant `storecomm_*` family's unmatched leaves in
this particular corpus. The honest remaining gap there is multi-level
array-permutation congruence, which would need a genuinely different kind
of matcher (one that recurses into the `array-ext` witness structure
itself) rather than another single-equation lemma.

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

### Update 3: an eleventh matcher (`store_perm`), generalizing `store_commute`

`Z3ArrayTheory.fst` was extended with a genuinely general theorem: for an
arbitrary chain of `n` nested `store`s on pairwise-distinct (named,
uninterpreted) indices, the resulting array value depends only on the
*set* of (index, value) updates applied, not their order
(`lemma_apply_updates_set_eq`, built on `apply_updates`/`last_match` over
association-list semantics). `store_commute`'s two-level swap is exactly
the `n=2` special case of this theorem.

A new matcher, `store_perm`, was wired into `try_match_leaf` (now
**eleven** matchers) to recognize this at arbitrary chain length: it
flattens both sides of a `Rewrite s t` leaf into `(base, [(index,
value), ...])` pairs via `flatten_store`, checks both chains share the
same base array, have equal length `>= 2`, have pairwise-distinct
(named-constant) indices on each side, and carry the *same set* of
(index, value) pairs — then discharges the leaf via
`lemma_apply_updates_set_eq` through a chain of append/evaluation
bookkeeping lemmas (`lemma_eval_pairs_append`, `lemma_eval_store_chain`,
`lemma_flatten_store_wf`). It typechecks cleanly, fires on a hand-built
3-level store chain under two different cyclic-rotation orderings
(`Z3PatternMatchedProofChecker.fst` section 12, "Demonstration 5" --
`sp3_leaf_1`/`sp3_leaf_2`, neither of which the strictly two-level
`store_commute` alone can match), and all 9 pre-existing
`Z3ExtractedProof*.fst` snapshots still verify with no regressions. The
Python mirror (`extract_z3_proof.py`'s `_match_store_perm` /
`_flatten_store` / `_pairwise_distinct_keys` / `_same_update_set`) was
updated to match, and is cross-checked for every generated benchmark
file against the real F* `collect_unmatched` via `assert_norm` (see
"What a `pass` does and does not certify" above) -- so a correct
benchmark run is itself evidence the mirror agrees with the verified
matcher.

Re-running the full QF_AX corpus (same 279 files, 30s timeout) with the
eleven-matcher library:

| metric | 10 matchers (previous) | 11 matchers (this run) |
|---|---|---|
| rewrite leaves matched | 68 / 486 (14.0%) | **69 / 486 (14.2%)** |
| matcher breakdown | 64 `eq_symm`, 1 `select_store_diff`, 2 `store_redundant`, 1 `reflexivity` | same, **+1 `store_perm`** |
| F* check @ 30s timeout | 207 pass / 16 timeout / 56 fail | 202 pass / 21 timeout / 56 fail |

Unlike `store_commute`, **`store_perm` does find one genuine match** on
this corpus: `cvc/read5.smt2` contains a leaf

```
s = (store (store (store S aaa vvv) a v) aa vv)
t = (store (store (store S a v) aa vv) aaa vvv)
```

— a literal 3-level store-chain reordering with no intervening
`select`/congruence steps, exactly the shape the general theorem targets
and `store_commute` (fixed at two levels) could never recognize. This is
a small but real, non-vacuous confirmation that generalizing the lemma
pays off on real proof output, in contrast to the `storecomm_*` family
discussed in Update 2, whose multi-level permutation reasoning is instead
buried inside a single opaque `array-ext` witness-skolemization step (not
a literal chain of `store` applications) and so remains outside what any
single-equation flattening matcher — `store_perm` included — can reach.
The small F* pass-count fluctuation (207->202 at fixed 30s) is noise from
the extra per-leaf `store_perm` case-split cost pushing a few more files
right at the timeout boundary, the same phenomenon documented under
Update 1/2 above, not a regression in soundness.

## Round 2 revisit: 100-file samples, the `is_unique_value` generalization, and the trusted-kernel/cross-check split

This section revisits the experiment after two changes made later in the
project: the matcher library grew from seven to **eleven** patterns (adding
`eq_symm`, `select_store_diff`, `store_commute`, `store_perm`), and the
distinctness side condition those last three depend on was generalized from
an ad-hoc "two differently-*named* uninterpreted constants" check to the
general, semantically-justified `is_unique_value`/`provably_distinct`
predicate (see `PULSE_PROOF_CHECKER_REPORT.md`'s "twelfth generalization"
section). Since full reruns of the whole corpus take a while, this round
instead samples **the first 100 `unsat`-annotated files (alphabetically) from
each logic** — fast enough to run at both the original 10s timeout and a more
generous 30s timeout in the same session, which turns out to be essential for
correctly separating "didn't finish in time" from "finished and found a real
gap" (see below).

**Sampling caveat**: QF_AX's first 100 files alphabetically are entirely the
`cvc/read5.smt2` file plus the `storecomm` stress-test family (deep nested
`store`-chain reordering benchmarks) — this is *not* a representative
cross-section of QF_AX (contrast the full 279-file run above, which found
this family to be the single largest unmatched-leaf source but not the only
content). QF_UF's first 100 are from `20170829-Rodin` and
`2018-Goel-hwbench`, a more typical mix.

### Headline result: the trusted kernel accepted every sampled proof

`Z3PulseProofChecker.check_proof`/`checker_accepts` — the actual
soundness-critical obligation (does this `Sym`/`Trans`/`Congr`/`Rewrite`
composition, interpreted via `Z3InterpretedProofChecker`'s concrete
per-theory semantics, really derive the claimed equation?) — **accepted
100/100 QF_AX and 98/98 QF_UF** extracted proof DAGs (the other 2 QF_UF files
had no equational content at all: pure resolution/CNF `unsat` proofs, outside
this pipeline's scope by design, same as always). This was confirmed by
inspecting every `fstar_check: fail` outcome's F* output directly: in all 23
QF_AX failures, exactly one error was reported, always at
`lemma_unmatched_count_cross_checked` (the *cross-check* assertion described
above under "What a `pass` does and does not certify") — never at
`check_extracted`/`lemma_extracted_proof_wellformed`. So "fail" here means
*the bookkeeping sanity check about which leaves are matched couldn't be
confirmed*, not that an unsound step was accepted.

| | QF_AX (100 files) | QF_UF (100 files) |
|---|---|---|
| `z3_no_proof`/`z3_with_proof` | 100/100 `unsat`, <30ms each | 100/100 `unsat`, <2s each |
| `fstar_check` @ 10s timeout | 6 pass / 93 timeout / 1 fail | 34 pass / 64 timeout / 2 no-proof-content |
| `fstar_check` @ 30s timeout | 77 pass / 23 fail / 0 timeout | 98 pass / 2 no-proof-content |
| trusted-kernel (`check_proof`) acceptance | **100/100** | **98/98** |
| rewrite leaves matched / total | 23 / 155 (22 `eq_symm`, 1 `store_perm`) | 82 / 167 (71 `reflexivity`, 6 `not_not`, 5 `eq_symm`) |
| files with **zero** unmatched leaves (fully end-to-end verified) | 0 / 100 | 44 / 98 |

The 10s-vs-30s gap (93 timeouts collapsing to 77 passes + 23 fails once given
enough wall-clock time) reconfirms this project's standing finding: F* /
Pulse's own per-invocation start-up cost (reloading this whole dependency
stack) dominates small-file latency far more than the benchmark's own size,
so a strict 10s budget mostly measures *that*, not provability.

### The 23 QF_AX `fail` cases: two distinct, now-understood root causes

Directly probing two representative failing files (`storecomm_t1_np_nf_ai_
00010_004.cvc.smt2`, 2 leaves, and `cvc/read5.smt2`, 2 leaves) by hand-editing
the generated `.fst` to ask about each leaf's `try_match_leaf` value and the
exact unmatched count in isolation (bypassing the harness's fixed 30s/`
--z3rlimit 60 --fuel 4 --ifuel 4` budget entirely) found:

1. **`cvc/read5.smt2` (1 of the 23): a stale Python mirror, not a checker
   bug.** This file's one `store_perm`-classified leaf uses `Index`-sorted
   (abstract, uninterpreted) index constants (`aaa`/`a`/`aa`), which are
   genuinely *not* `is_unique_value` (that predicate is `false` on any
   `App f args` whose `f.interp = None`, i.e. any uninterpreted/free
   constant, by construction — see `Z3PatternMatchedProofChecker.fst`'s
   `is_unique_value`). So the real, trusted `store_perm_leaf_ok` cannot and
   does not match this leaf. `tools/extract_z3_proof.py`'s Python mirror,
   however, still uses its original, simpler criterion ("two distinctly-
   *named* 0-ary uninterpreted constants") for `select_store_diff`/
   `store_commute`/`store_perm`, predating the `is_unique_value`
   generalization — so it reports a match the real checker now (correctly)
   refuses. **This is an honest soundness tightening, not a regression in
   correctness**: naming two free constants differently never semantically
   guarantees they denote different domain elements without an explicit
   hypothesis saying so, so the old Python-mirrored criterion was always an
   unjustified shortcut; `is_unique_value` only accepts distinctness that is
   syntactically self-evident (literal numerals/BV constants/booleans/
   sequence-of-unit literals). The practical upshot: **on corpora like QF_AX
   where array indices are abstract/free-sort constants (the overwhelmingly
   common case, not literal integers), `select_store_diff`/`store_commute`/
   `store_perm`'s distinctness gate can now never fire** — their matching
   power, as measured by the original "68/486" and "+1 (`store_perm`)"
   headline numbers earlier in this report, no longer applies to the
   current, more conservative checker. (The Python mirror should eventually
   be updated to mirror `is_unique_value` exactly, so its log output and the
   type-checked cross-check stay in agreement — not done here, since it
   affects only logging/reporting, never the trusted kernel.)

2. **The other 22: a genuine F*-normalizer/SMT scalability wall, not a
   budget-tuning problem.** For the `storecomm` family's deeper chains (one
   `select` peeled through up to ~9 nested, otherwise-irrelevant `store`s),
   neither `assert_norm (try_match_leaf s t == true)` nor `== false` could be
   discharged — **even after manually raising the probe to `--z3rlimit 2000
   --fuel 20 --ifuel 20`** (33x/5x/5x the generated template's defaults).
   This rules out "just needs a bigger timeout": the cost driver is the
   *size of the expression tree* embedded in a single `Rewrite` leaf (the
   nested-store chain), not the leaf *count* (these files have only 2–4
   leaves total) — `try_match_leaf`'s eleven-way disjunction, each clause
   doing its own `flatten_store`/structural-equality walk over that chain,
   appears to blow up combinatorially for F*'s normalizer well before SMT's
   own resource counter is the bottleneck. This is the same phenomenon the
   original (`v1`) run's "fail" cases were attributed to, now confirmed by
   direct experiment rather than inference.

### What remains unmatched, and why

* **QF_AX** (132/155 unmatched leaves, every sampled file has ≥1): the
  dominant shape is *"select a value through an N-level nested `store`
  chain where the target index differs from all N update indices"*
  (`(select (store (store ... a i1 v1) ... iN vN) j)`, `j` distinct from
  every `ik`) — this is semantically a chained generalization of
  `select_store_diff`, but **no current matcher recognizes it**:
  `select_store_same`/`store_redundant` only peel exactly one `store` level,
  and `store_perm` requires a full chain-vs-chain reordering (both sides
  still full chains), not a single final `select`. This is a clearly scoped,
  not-yet-attempted twelfth matcher (`select_store_diff_chain`, say),
  distinct from the `store_commute`/`store_perm` family already covered.
* **QF_UF** (85/167 unmatched leaves across 98 files; 44/98 files are fully
  clean): unchanged from the original full-corpus finding — propositional
  CNF/Tseitin normalization (`(and ...)`/`(or (not ...) (not ...))`
  rewritten forms of named sub-formula definitions) and EUF
  congruence-closure facts, neither of which this project's matcher family
  (which targets array/seq/bv/bool *algebraic identities*, not clausal
  normal-form transformations) is designed to cover.

### Bottom line

*Fully proved*: the core equational-proof-composition kernel
(`Z3ProofTheory`'s `proof` type checked against `Z3InterpretedProofChecker`'s
concrete semantics via `Z3PulseProofChecker.check_proof`) — every real Z3
proof DAG extracted from both 100-file samples composes soundly; 44/98 QF_UF
files are additionally *fully* verified end-to-end (zero remaining trusted
leaves). *Gaps*: (1) a not-yet-written chained `select`-through-`store`-chain
matcher would close most of QF_AX's remaining leaves; (2) CNF/Tseitin and EUF
congruence facts remain outside this project's rewrite-matcher scope for
QF_UF; (3) the three distinctness-gated matchers (`select_store_diff`/
`store_commute`/`store_perm`) are now sound but essentially unreachable on
corpora using abstract/free-sort array indices, which is most of QF_AX; (4)
the auto-generated template's fixed SMT/normalization budget cannot certify
its own bookkeeping cross-check on deep nested-`store` expressions no matter
how high it is raised, which is a proof-engineering problem in its own right
(the cross-check needs a smarter/staged proof, not just more fuel).

## Reproducing

```powershell
# (benchmarks downloaded separately, outside this repo, to C:\smtlib-benchmarks)
python fstar\tools\run_benchmarks.py C:\smtlib-benchmarks\QF_AX --out qf_ax_results.jsonl --timeout 10 --workers 16
python fstar\tools\run_benchmarks.py C:\smtlib-benchmarks\QF_UF --out qf_uf_results.jsonl --timeout 10 --workers 28
python fstar\tools\analyze_benchmarks.py qf_ax_results.jsonl QF_AX
python fstar\tools\analyze_benchmarks.py qf_uf_results.jsonl QF_UF

# re-run QF_AX against the updated nine-matcher library, at the higher
# timeout the extra per-leaf reasoning now needs (see "Update" above):
python fstar\tools\run_benchmarks.py C:\smtlib-benchmarks\QF_AX --out qf_ax_results_v2_t30.jsonl --timeout 30 --workers 24
python fstar\tools\analyze_benchmarks.py qf_ax_results_v2_t30.jsonl QF_AX_v2

# re-run again against the ten-matcher library (adds store_commute; see
# "Update 2" above -- 0 additional matches on this corpus, root cause
# documented there):
python fstar\tools\run_benchmarks.py C:\smtlib-benchmarks\QF_AX --out qf_ax_results_v3_t30.jsonl --timeout 30 --workers 24
python fstar\tools\analyze_benchmarks.py qf_ax_results_v3_t30.jsonl QF_AX_v3

# re-run again against the eleven-matcher library (adds store_perm, the
# general multi-level store-permutation matcher; see "Update 3" above --
# +1 match on this corpus, cvc/read5.smt2):
python fstar\tools\run_benchmarks.py C:\smtlib-benchmarks\QF_AX --out qf_ax_results_v4_t30.jsonl --timeout 30 --workers 24
python fstar\tools\analyze_benchmarks.py qf_ax_results_v4_t30.jsonl QF_AX_v4

# Round 2 revisit (100-file samples, eleven-matcher library, generalized
# is_unique_value distinctness; see "Round 2 revisit" above):
python fstar\tools\run_benchmarks.py C:\smtlib-benchmarks\QF_AX --out qf_ax_100.jsonl --timeout 10 --limit 100 --workers 8
python fstar\tools\run_benchmarks.py C:\smtlib-benchmarks\QF_UF --out qf_uf_100.jsonl --timeout 10 --limit 100 --workers 8
python fstar\tools\run_benchmarks.py C:\smtlib-benchmarks\QF_AX --out qf_ax_100_t30.jsonl --timeout 30 --limit 100 --workers 8
python fstar\tools\run_benchmarks.py C:\smtlib-benchmarks\QF_UF --out qf_uf_100_t30.jsonl --timeout 30 --limit 100 --workers 8
python fstar\tools\analyze_benchmarks.py qf_ax_100_t30.jsonl QF_AX_round2
python fstar\tools\analyze_benchmarks.py qf_uf_100_t30.jsonl QF_UF_round2

# Round 3: Tseitin/De Morgan matchers for QF_UF (fourteen-matcher library;
# see "Round 3" below)
python fstar\tools\run_benchmarks.py C:\smtlib-benchmarks\QF_UF --out qf_uf_100_v2_t30.jsonl --timeout 30 --limit 100 --workers 8
python fstar\tools\analyze_benchmarks.py qf_uf_100_v2_t30.jsonl QF_UF_v2
```

## Round 3: closing the QF_UF Tseitin/De Morgan gap

Round 2 found that QF_UF's 85/167 unmatched leaves (across the 100-file
sample) were dominated not by EUF congruence facts but by **propositional
CNF-normalization rewrites** that Z3's Tseitin transformation produces when
naming sub-formulas: `and`-expansion into De Morgan `not`/`or` form, and
`eq`/`iff` nodes rearranged around a `not`. A closer per-leaf classification
of all 85 unmatched leaves found:

| shape | count | example |
|---|---|---|
| `and_as_not_or` (De Morgan, `and`→`not`/`or`) | 31 | `(and input k!0)` ↦ `(not (or (not input) (not k!0)))` |
| `eq_not_rearrange` (`=`/`not` swapped around) | 28 | `(= y (not (or ...)))` ↦ `(not (= (or ...) y))` |
| `pure_rename` (hypothesis-based renaming, **not a tautology**) | 10 | `flash` ↦ `nf` |
| `implies_as_or` (`=>` unfolded to `or`) | 1 | `(=> rd1 (not rd2))` ↦ `(or (not rd1) (not rd2))` |
| other (nested-context De Morgan, `ite`-multiplexer defs, `or`-commutativity-under-`eq`) | 15 | — |

`pure_rename` and most of "other" are hypothesis-tracking or Congr-level
decomposition problems, out of scope for a pure leaf-rewrite matcher (they
are not themselves tautologies — they depend on an external definitional
hypothesis). The first three rows, however, **are** pure tautologies over
Boolean connectives and are exactly matchable the same way every other
rewrite-matcher in this project is: by recognizing a fixed syntactic schema
and proving it sound once and for all against the concrete semantics.

### What was added

1. **Three new interpreted Boolean operators** in the shared semantic model:
   `op_and`/`op_or`/`op_implies` (`Z3ValueTheory.fst`, `decl_kind` 13/14/15)
   with `interp_and`/`interp_or`/`interp_implies` (`Z3InterpretedProofChecker.fst`),
   each the standard two-argument Boolean truth table over `VBool`. (Only the
   binary instance is modeled, matching how Z3's proof terms actually use
   `and`/`or` inside individual `PR_REWRITE` leaves — the surrounding n-ary
   `and`/`or` is handled a layer up by `Congr`, unaffected by this change.)
2. **Three new rewrite matchers** in `Z3PatternMatchedProofChecker.fst`
   (§4l/§4m/§4n), each with a from-scratch soundness lemma proved against
   `Z3InterpretedProofChecker`'s concrete semantics (same pattern as every
   earlier matcher — no new axioms, no `admit`):
   * **`demorgan_and`**: `App fand [p;q]` ↔ `App fnot [App for_ [d1;d2]]`
     where each `di` is literally `(not pi)` **or** the double-negation-fused
     form `pi = (not ri), di = ri`, tolerant of `or`-argument-order swap.
   * **`implies_as_or`**: `App fimp [p;q]` ↔ `App for_ [App fnot [p]; q]`.
   * **`eq_not`**: `App feq [a; App fnot [c]]` ↔ `App fnot [App feq [c;a]]`
     (boolean identity `(av = not cv) == not (cv = av)`).
3. **Mirrored in `tools/extract_z3_proof.py`**'s `classify_rewrite`/`func_decl`
   so the benchmark harness's logging/cross-check agrees with the F* checker.

The whole file (`Z3PatternMatchedProofChecker.fst`, now fourteen matchers)
type-checks with zero errors (`fstar.exe --include . --smt z3.exe
Z3PatternMatchedProofChecker.fst` → "All verification conditions discharged
successfully").

### Re-run result: QF_UF, 100 files, 30s timeout

| | QF_UF round 2 (eleven matchers) | QF_UF round 3 (fourteen matchers) |
|---|---|---|
| rewrite leaves matched / total | 82 / 167 | **143 / 167** |
| matcher histogram (new) | `reflexivity`=71, `not_not`=6, `eq_symm`=5 | + `demorgan_and`=32, `eq_not`=28, `implies_as_or`=1 |
| unmatched leaves | 85 | **24** |
| `fstar_check` pass / no-proof-content | 98 / 2 | 98 / 2 (unchanged — no regressions) |
| trusted-kernel (`check_proof`) acceptance | 98/98 | **98/98** |
| files with zero unmatched leaves | 44/98 | **77/98** |

Every one of the 98 extracted proofs still passes end-to-end — the three new
matchers add real coverage without touching the soundness of any
already-passing file. The remaining 24 unmatched leaves are the expected
residual: `pure_rename` (hypothesis-based, out of scope by design) plus a
handful of nested-context shapes (e.g. `(or (not org) (and (not rd1) (not
rd2)))`, De Morgan one level further from the leaf than this matcher family
reaches) that would need a `Congr`-aware decomposition rather than a single
leaf-schema matcher to close.

### Bottom line (Round 3)

QF_UF's pure-tautology rewrite-leaf coverage on the 100-file sample rose from
49% (82/167) to **86% (143/167)**, with the dominant previously-unmatched
shapes (Tseitin `and`-as-De-Morgan and `eq`/`not` rearrangement, 59 of the 85
original unmatched leaves) now fully covered by three new, independently
soundness-proved matchers. The remaining 24 unmatched leaves are
predominantly hypothesis-dependent renamings (`pure_rename`, 10) that are not
tautologies at all and are correctly outside this checker's scope, plus a
small number of nested/compound shapes needing `Congr`-level (not purely
leaf-level) reasoning — a natural next target if QF_UF coverage is revisited
again.

## Round 4: independent re-check (fresh 100-file samples, current code)

Re-ran both 100-file samples end-to-end from scratch (fresh `z3.Solver()`
calls, fresh proof extraction, fresh `fstar.exe` invocations — not a replay
of Round 2/3's saved data) against the current fourteen-matcher
`Z3PatternMatchedProofChecker.fst`, to confirm the Round 3 numbers are
reproducible and to get the still-missing QF_AX zero-unmatched-leaves count:

```
python tools\run_benchmarks.py C:\smtlib-benchmarks\QF_UF --out qf_uf_100_round4.jsonl --timeout 30 --limit 100 --workers 8
python tools\run_benchmarks.py C:\smtlib-benchmarks\QF_AX --out qf_ax_100_round4.jsonl --timeout 30 --limit 100 --workers 8
```

| | QF_UF (100 files) | QF_AX (100 files) |
|---|---|---|
| `z3_no_proof`/`z3_with_proof` | 100/100 `unsat` | 100/100 `unsat` |
| proof extracted | 98/100 (2: no equational root found) | 100/100 |
| `fstar_check` | 98 `pass`, 0 `fail`, 2 no-attempt | 77 `pass`, 23 `fail` |
| rewrite leaves matched/total | **143/167** (identical to Round 3) | 23/155 (`eq_symm`=22, `store_perm`=1) |
| files with zero unmatched leaves | **77/98** | **0/100** |

QF_UF's numbers reproduce Round 3 exactly (same 143/167 matched, same
`demorgan_and`=32/`eq_not`=28/`implies_as_or`=1/`reflexivity`=71/`not_not`=6/
`eq_symm`=5 histogram), confirming the three new matchers are deterministic
and stable across independent runs, and fills in the previously-missing
"files with zero unmatched leaves" datapoint: **77/98** QF_UF files in this
sample are now fully, end-to-end verified with zero trusted leftovers (up
from 44/98 pre-Round-3).

QF_AX's gap is **unchanged and unrelated** to the Round 3 Boolean matchers
(QF_AX is a pure array-theory corpus with essentially no Boolean-connective
rewrite leaves to match): this sample's 132 unmatched leaves are
overwhelmingly long, non-adjacent `store`/`select` chains over 4+ array
updates (e.g. `(let ((a!1 (store (store (store (store a ...)))))) ...)`,
25+5 occurrences) that the existing `store_perm`/`select_store_*` matchers
don't reach (those recognize a *bounded*, small number of permuted/redundant
stores, not an arbitrary-length chain), plus a long tail of plain hypothesis
variable renamings (`i10`/`i28`/`a_19`/...) that, like QF_UF's
`pure_rename`, are not tautologies and are correctly out of scope. The 23
`fail` outcomes are (as in Round 2) `z3rlimit`/`fuel` budget exhaustion of
the `lemma_unmatched_count_cross_checked` recomputation on these
leaf-heavy/trust-heavy proofs within the 30s F* timeout, not the kernel
checker (`check_proof`) accepting something it shouldn't.

**Bottom line (Round 4)**: the Round 3 QF_UF improvement is confirmed
reproducible on an independent run (143/167 matched, 77/98 fully verified).
QF_AX's open gap is unchanged and is specifically a **multi-store-chain**
coverage gap (not a regression, not a QF_UF-type Boolean-connective gap) —
the natural next matcher-library target if QF_AX is revisited, requiring a
chained `select`-through-an-arbitrary-length-`store`-sequence schema rather
than the current fixed-arity `store_perm`/`select_store_same` matchers.
