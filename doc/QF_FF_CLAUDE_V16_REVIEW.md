# Review of the updated Claude finite-field backend (12 patches)

**Recommendation: retain the improvements, but do not merge this version unchanged.**
The fresh primary campaign gains 46 solutions and substantially reduces aggregate
time. A held-out circuit, however, regresses from 0.27 seconds to repeated
10-second timeouts, and a new deep-expression test crashes. Both regressions
are isolated to the new default uniqueness tactic. Compiler portability and
F4 resource guards from the earlier review also remain unresolved.

This is the historical review of the submitted version, before corrections.
The findings below are addressed in the subsequent
[corrected backend report](QF_FF_BACKEND_CORRECTIONS.md).

## Fresh measurements

Same native arm64 machine, two frozen configurations, identical input bytes,
10-second external deadlines, four workers and a deterministic shuffled schedule.
The previous configuration is the archived six-patch Claude candidate; the latest
contains all twelve supplied patches. All 4,424 primary runs completed.

| Family | Distinct inputs | Previous six patches | Latest twelve patches |
|---|---:|---:|---:|
| Public determinism circuits | 782 | 702 | **720** |
| Public soundness circuits | 771 | 752 | **754** |
| FFSAT small-field systems | 325 | 271 | **297** |
| Generated dense systems | 28 | 27 | 27 |
| Generated underdetermined systems | 6 | 6 | 6 |
| Exhaustive-oracle fuzz cases | 200 | 200 | 200 |
| Large-field differential cases | 100 | 100 | 100 |
| **Total** | **2,212** | **2,058** | **2,104** |

There are **46 gains, zero losses, zero SAT/UNSAT disagreements, zero process
errors and zero known-oracle mismatches in this primary campaign**. The new
solutions comprise 25 UNSAT and 21 SAT answers. Seventeen gains are closed
directly by `ff-unique`; this is observed attribution, not a complete ablation
of the other interacting changes.

On the same 2,058 shared successes, cumulative wall time falls from **330.204 s
to 132.883 s**, a **59.8% reduction**. The median paired ratio is **0.9971**:
the large aggregate improvement is concentrated in harder cases, rather than a
uniform speedup of every input. Five primary pairs exceeded 2x and 0.2 s of
additional elapsed time. Three serial repeats confirm one smaller regression:
`compilation-deterministic-none-06v-128t-ff-circ-255b-0s.smt2` rises from
0.036 to 0.179 s; disabling uniqueness restores 0.036 s. The other four
primary outliers do not reproduce in the serial repeats. Primary measurements
have not been replaced by follow-ups.

Weighted by the original 1,927 public member paths, coverage is **1,774 versus
1,820**, reproducing the latest supplied coverage count on our corresponding
local corpus. As in the earlier review, the ZIP does not contain the benchmark
source bytes, so this does not establish byte identity with the author's runs.

The old binary solved 2,059 cases in the September 28 campaign and 2,058 in this
fresh rerun. The sole status difference is `testdata_r_13_32_16.014.smt2`:
SAT in 8.895 s previously, timeout now. Thus the fresh paired gain is 46;
the coverage difference against the earlier published count is 45. Our own
pre-F4 fork's earlier 2,010 result was not remeasured in this campaign.

## Held-out coverage exposes an important regression

The same independent 32-input CAV24 screen used in the first review gives
**28/32 previous versus 27/32 latest**: one lost QED²/Picus circuit. Counts are
unchanged for ASHR (5/6), Examples (6/6), and Seq (8/8); QED² drops from 9/12
to 8/12. The shared 27 successes take 1.841 versus 5.190 seconds cumulatively.

Serial follow-ups use three runs per configuration and retain their medians:

| Input | Previous | Latest | Latest, uniqueness disabled |
|---|---:|---:|---:|
| `Bits2Num_strict@bitify@circomlib.smt2` | **0.268 s** | **timeout, 3/3** | **0.269 s** |
| `Bits2Num@bitify@circomlib_254.smt2` | 0.079 s | 1.915 s | 0.081 s |
| `bitsum_21_layers_5.smt2` | 0.067 s | 0.519 s | 0.066 s |
| `bitsum_16_layers_4.smt2` | 0.043 s | 0.267 s | 0.044 s |

The ablation changes only the tactic parameter, using
`(check-sat-using (with default :ff.unique false))`. It does not disable F4,
tiny-field search, random slicing or the encoding caches. These repeatable
results isolate uniqueness as the cause. Across primary and held-out inputs
together, the fresh totals are **2,085/2,243 versus 2,130/2,243**, with 46 gains
and one loss. One input occurs in both screens and is counted once in these
combined totals. This number excludes the separate crash stress test.

## Changes needed before integration

1. **Prevent the uniqueness encoder's stack overflow.** Its recursive AST walk
   (`src/tactic/arith/ff_unique_tactic.cpp:529`, recursive call at line 554)
   crashes on a valid input containing 60,000 nested `ff.neg` applications over
   F257. The input is simply an even number of negations of `x`, asserted equal
   to one, with `x != 0`; it has the model `x = 1`. The previous executable
   returns SAT; the latest exits with SIGSEGV (-11). Running `ff-unique` alone
   also crashes, while disabling it returns SAT in 0.105 s. Use an iterative
   DAG walk, or a guarded fallback before exceeding the stack. Add this input
   as a regression test. Shallower 4,000- and 12,000-level checks pass.
2. **Bound the default uniqueness pass and preserve the cheap existing path.**
   The 50,000-node/16-level Boolean search bounds do not cap the work inside
   one propagation node. Encoding, canonicalization and gadget matching also
   need explicit work/size limits and prompt cancellation. Consider running
   cheap existing simplification first, followed by a bounded uniqueness
   attempt that leaves the original goal available on exhaustion. Validate
   the policy on both the primary and held-out inputs; do not special-case
   circuit names. Merely reducing split depth will not address all costs:
   the slower 254-bit Bits2Num example is decided in one uniqueness node.
3. **Finish compiler portability.** `ff_field.h` still unconditionally uses
   GNU/Clang 128-bit integer types. The new `ff_tiny.cpp` additionally uses
   unguarded `__builtin_ctzll` and `__builtin_popcountll` (lines 106, 121, 152,
   162). Native MSVC needs portable operations or a capability-gated fallback;
   a runtime flag cannot fix compilation. This is a source-level finding, not
   a Windows build performed in this review.
4. **Retain the earlier resource-guard work.** The F4 variable cap still
   precedes addition of disequality auxiliaries; monomial admission is not
   guarded at every interning site. The new recursive tiny-field search also
   warrants an explicit depth/stack policy. No tiny-search crash was observed
   in this review; the demonstrated crash is specifically in uniqueness.

The `ff.unique` options are tactic parameters, not registered `smt` parameters:
`smt.ff.unique=false` currently exits with an unknown-parameter error. Document
the working tactic form or register a consistent public option before release.

## Correctness and certificate scope

No wrong SAT/UNSAT result was observed in the tested cases. Random slices return
only verified SAT models; failed slices return unknown and are not used as
global UNSAT evidence. Tiny-field UNSAT exhausts finite domains, while its SAT
assignments pass the engine's existing input verification. Binary uniqueness
checks the non-wrapping range condition. These are useful design choices,
not a formal proof of the implementation.

**The new Python checker is not certificate production by the C++ solver.**
`check_unique_certificates.py` independently regenerates a Python derivation
and asks another solver about its local implications. It neither consumes
a trace emitted by `ff-unique` nor connects those steps to the existing
Alethe/PAC bundle. F4 row multipliers, root partitions, tiny-domain branch
discharge and uniqueness derivations still need production and end-to-end
checking. The native tactic explicitly skips goals with native proofs enabled.
None of the ordinary-solving coverage gains above is counted as a certificate
coverage gain, and no new Lean integration was evaluated here.

## Tests completed

* Release `test-z3 finite_field`: passes, including the supplied 600 tiny-field
  exhaustive comparisons, 900 direct F4 comparisons, arithmetic and existing
  certificate/basis/model checks.
* 214 fresh, independently evaluated gadget/bit-range inputs: 428 checks using
  full solving and the uniqueness tactic alone. Full solving returns 143 SAT
  and 71 UNSAT; uniqueness closes 68 UNSAT cases and leaves 146 unknown.
* 32 fresh quadratic systems over 65537, 4294967291, 4294967311 and
  18446744073709551557: 96 runs of previous, latest and cvc5 1.4.0; no answer
  disagreement or planted-model mismatch. This screens the delayed-reduction
  threshold and arithmetic representation boundary. It is not a fresh broad
  cvc5 performance comparison.
* 15 existing UF/array/incremental checks over five fields and logic-alias
  equivalence: pass.
* 272 additional answers per executable across scoped redeclarations,
  changing field sorts, different wire definitions, push/pop and reset:
  all 544 answers match the expected sequence.
* Literal external proof suite: 29 valid bundles accepted, 25 invalid cases
  rejected; the previously documented Carcara input-binding gap remains
  guarded by independent replay.
* Boolean external proof suite: 30 accepted, 22 rejected, 575 search checks,
  depth-12,000 let input and 400-node sharing chain. The exhaustive mixed sample
  retains the two expected unavailable proofs (27 SAT, seven certified UNSAT).
* Resource probes: repeated-squaring inputs and shallower ASTs terminate;
  the 60,000-level uniqueness crash above remains an explicit failing test.

## Provenance and reproduction

Submission SHA256:
`8446c74e25fc836a2bd59c818c48969c39e91b3c916f6ba1774f12b97315da51`.
The first six patch diffs are identical to the earlier submission. Patches
7–12 were applied to the previous isolated integration atop `6400f1a42`,
retaining both certificate code and candidate code. No algorithm edits were
made to the measured candidate. The current fork's intervening commit changes
only the earlier review documentation.

Latest executable SHA256:
`aab6967f070dd03ddaa98df6a50882dcfcab768d9425ea361693d7c2ad5d0dd7`.
Build: Apple Clang, native arm64, Release, CMake/Ninja, explicit Xcode macOS SDK.
The initial build started before the last patch's application completed and
needed reconfiguration; the final build and all measurements include all
twelve patches. Build logs preserve that history.

The strict runner requires exit zero, exactly one answer and no SMT error;
timeouts retain actual elapsed time. Successful primary runs all finish below
ten seconds. The four-worker campaign was not run on an exclusively reserved
machine; short independent correctness probes also ran during parts of it.
Use the serial follow-ups to assess individual small-time outliers. The primary
campaign did not sample RSS and is not a memory comparison.

Evidence is archived under
`tests/finite_field/results/claude-f4-review-20260929/`: input bytes, commands,
input/binary hashes, all stdout/stderr receipts, per-run metadata, paired
summaries, held-out results, serial ablations, crash reproducer, test logs,
exact integrated patch and the original ZIP. Bulky evidence remains ignored by
Git. The main fork's solver files and default settings are unchanged.

* [Primary paired results](../tests/finite_field/results/claude-f4-review-20260929/measurement/summary.json)
* [Held-out paired results](../tests/finite_field/results/claude-f4-review-20260929/holdout/summary.json)
* [Held-out serial ablations](../tests/finite_field/results/claude-f4-review-20260929/holdout-serial/results.json)
* [Crash reproducer](../tests/finite_field/results/claude-f4-review-20260929/resources-deep/negations-60000.smt2)
* [Crash isolation](../tests/finite_field/results/claude-f4-review-20260929/resources-deep/isolation.json)
* [Exact tested patch](../tests/finite_field/results/claude-f4-review-20260929/provenance/integrated-candidate.patch)
