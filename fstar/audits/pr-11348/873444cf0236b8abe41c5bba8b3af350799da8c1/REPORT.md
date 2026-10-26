## Scope
Base compare 3150a4b..873444c. Only C++ change: src/qe/qsat.cpp (~line 1278): added fail_if_proof_generation("qsat", in) after tactic_report; removed stale TBD comment. Source sha256 of head file (raw) 8feb195846dc08109911e93aece98d463b61cf70823c3c39b9c4122a6be7d9c2 (note: saved copy was JSON-wrapped contents API response).

## Obligations (all proved)
1. proofs enabled => throws tactic_exception (tactic.cpp:284 checks in->proofs_enabled()).
2. proofs disabled => proceeds unchanged.
3. body unreachable with proofs enabled.

## Assumptions
fail_if_proof_generation throws iff goal proofs_enabled (read from trusted base tactic.cpp). Standard F* library.

## Exclusions
All non-C++ files changed (Z3ArithmeticRewrite.fst, Z3ProofDocument.fst, Z3ResolutionProof*.fst, Z3SortedProof.fst, OCaml runtime/tools, docs). Not mechanized C++ verification; soundness benefit (qsat ignoring proofs) manually reviewed only.

## Commands
F* 2026.09.27, Z3 4.13.3 independent backend.
timeout 120 /tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --include /home/runner/work/z3/z3/fstar --z3rlimit 10 --cache_dir cache --odir out Z3Pr11348Qsat.fst
