# F* audit of PR #11524 @ ec09d65d8edb675dcce8504dd4d8f2b2446f4cc4 (base b4eb6736)

**Scope: partial.** PR touches ~30 files (~8k added lines). One changed function audited: the native binding `z3_name_units_scan_counted` / `Scan.scan` (fstar/cherry_runtime/kernel.c; fstar/ocaml_runtime/Z3NameUnits.ml) realizing Z3NameUnits.scan_units. Snapshot hashes (sha256): Z3NameUnits.fst 38bdc522..., Z3DagGuardKernel.fst d80ec9d6... (fetched, not audited).

## Obligations
1. O1 scan loop returns (k+units<=cap ? k+units : -1): **proved** (lemma_scan).
2. O2 the clamp of cap to byte size n is exact for every nat limit, so result == `if strlen<=limit then strlen else -1` (the .fsti spec): **proved** (lemma_scan_units).
3. O3 lead-byte reads <= min(strlen, limit) and loop terminates (step strictly advances): **proved** (lemma_reads, termination).

No counterexample found; refutation attempt: none reachable in the model.

## Correspondence / assumptions
- F* `width`, `step`, `scan` mirror the C/OCaml code (width thresholds 0x80/0xE0/0xF0; clamped advance `width < n-i ? i+w : n`). `units` is *assumed* to be FStar.String.strlen's decoder (not mechanized against FStar.String); bytes modelled as a seq of 0..255.
- Not mechanized: C/OCaml execution, cherry_int/Zarith representation (the C `cherry_int_to_u64(limit)` when limit < n, and the 2^57 < CHERRY_INT_MAX claim), memory safety, extraction equivalence, tests.
## Exclusions (not audited)
Z3DagGuardKernel, Z3CheckedGuardKernel, Z3DagDocument, Z3DagScope, Z3Checked*, Z3VerifiedDocument, Z3NativeProof, Z3Cherry diagnose_dag/diagnose_verified, main.cpp, tests.cpp, OCAML_CHECKER_REPORT.md, and all other changed files. Their proofs were not rechecked; no claim of PR safety.
## Reproduce
See verification log. Versions: F* 2026.09.27, Z3 4.13.3 (pinned release).
