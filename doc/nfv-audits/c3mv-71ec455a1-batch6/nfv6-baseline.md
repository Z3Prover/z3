# Batch 6 baseline reconciliation

Status: complete, source-only. No property selected, modeled, proved or refuted; no verifier invocation or production execution. Continuous schedule 2 remains active. This stage reconciles a changed comparison baseline without modifying any earlier publication.

## Pins and exact comparison

The audited production revision remains `71ec455a18702fe695d0c924a535ff9f385bd58d`; current `c3mv` publication HEAD is `4be813a75bdc59574df23da8ce5805a262171ba9`. Both have source tree `caa5a9922f074f9f4adc8f7c98e1685be9626503`. Old comparison master is `c2460a558fc6fee3cf15cfebd2d3f642ebf77770`; fetched new master is `bcad05a7bf7dd9b82bd7a665018e0480e737264b`. The merge base remains `437536cd64a544a1c329fc57d83e56e294fdf47c`.

| Comparison | All changed files | Under src |
| --- | --- | --- |
| Merge base to audited source: branch-introduced delta | 104 | 89 |
| Old master to audited source: previous direct comparison | 110 | 93 |
| New master to audited source: current direct comparison | 120 | 103 |

The direct comparison includes changes introduced only on master; it is not the branch-authored delta. No old proof result, conditional model refutation or report is relabeled as covering the new master. NFV methodology remains pinned to microsoft/neuro-formal-verification at `599726579274cfeb1c0915414b911371527a9870`.

## Master advance reviewed as text

Two commits advance master: `b360da09571e53e10e40d8e925701ef6e035113d`, QFBV default params (#11781), and `bcad05a7bf7dd9b82bd7a665018e0480e737264b`, Prevent wrong sat for lambda arguments to uninterpreted functions (#11744). Thirteen paths change: seven production files, five tests and one test CMake file. The complete production delta was read, and the complete src delta is retained as `nfv6-master-drift.patch`.

The seven production paths are `solve_eqs.cpp`, `tactic_cmds.cpp`, `theory_array_full.cpp`, `qfbv_tactic.cpp`, `tactic.cpp`, `tactic.h` and `tactical.cpp` (full paths and all blob IDs are in `nfv6-baseline.json`). Their `c3mv` blobs equal the old-master blobs exactly. Consequently the newly fetched changes are missing upstream changes, not newly authored c3mv regressions.

The QFBV commit changes tuned settings to overridable defaults while retaining forced settings; adds module-key parameter descriptors; and changes tactic-display parameter/annotation handling. The array change inspects lambda equivalence-class root parents and no longer excludes uninterpreted-function parents in that check. These are source-diff observations, not independent correctness proofs, reproductions or new findings against c3mv. No native test was run and no upstream fix was applied.

The only intersections between the new master delta and the branch-introduced path set are `src/test/CMakeLists.txt`, `src/test/main.cpp`, and `src/test/smt_context.cpp`. There is no intersection with any of the 14 primary entry paths in the 22 selected intents P1-P22. P20-P22's batch-5 retranslations are counted once. Path nonintersection does not establish semantic independence, absence of shared helper effects, native integration correctness, or exhaustive coverage.

## Genuine continuation, not another proof retry

The batch-2 and batch-3 coverage ledgers were read together with actual P1-P22 property metadata. Their historical candidate statuses are not treated as current results. In particular P13, P18, P20, P21 and P22 retain their earlier unresolved status, and conditional model refutations do not become native bug reports.

Next stage is **nfv6-coverage**, a bounded source-only refinement of still-unselected entry scopes:

1. C05: `stoi_facet::check_stoi_coherence`, conversion-term tracking and callback-induced appends/reallocation. Inspect actual saved values, loop bounds and callers rather than assuming reference stability.
2. C13: `seq_model_value_proc::mk_value`, producers and consumers of nested power slots. Inspect balanced-stack assumptions and word/exponent semantics; P8's different pending-result entry in the same file does not cover this function.
3. C14: `regular_compiler::bounded_length` and the nonnegative decimal-language construction, separately. Preserve saturation/overflow behavior, leading zeros and applicable input contracts. P9 covers negative thresholds, not these entries.

This is not a frozen property selection or a quota of three proofs. The next stage must verify changed-span eligibility and inspect helpers/callers before proposing any complete property. Selection, modeling, validity/domain gates and whole-property verification remain later separate stages. Do not retry sealed batch-5 domain checks without a genuinely distinct, preplanned proof approach, and do not count retranslations as new source coverage. Other remaining areas and native applicability questions stay open.

## Evidence and preservation

`capture_nfv6_baseline.py` derives identifiers/path sets locally, captures narrow old/new/source blob identities, records exact commit metadata and all comparison paths, and retains the complete raw master-drift patch. It checks branch, HEAD, source-tree identity, clean worktree, stash, ancestry and merge base. `nfv6-baseline.json` records all five prior report tree IDs and current selected entry spans. These are Git/provenance checks, not formal verification.

Fetch was limited to master into its remote-tracking ref: no checkout, pull, merge, rebase, reset, forced update, stash modification or production patch. Source remains immutable text. The user stash remains `7af7fad70e9cea38601c67ff00d89f6b5576c2d6`; all five published report trees and the worktree are unchanged.
