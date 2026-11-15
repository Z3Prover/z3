## Scope
- Head SHA 28ff80e4aab23343dfabb76314aae29281f22c99; base SHA f46b3c58e41c0f9531cbb7cbab243b8cd2a98250.
- The PR was open at that SHA and had no existing `fstar-nfv-audit:<head-sha>` comment.
- Tooling: F* 2026.09.27 with the pinned Z3 4.13.3 backend.

## Findings
- 428 of 429 changed files are under `fstar/`: proof modules, markdown reports and CSV. They add or modify checker/proof artifacts and remove some modules.
- The only non-fstar change is `src/api/ml/CMakeLists.txt`. It drops the `execute_process` call to `ocamlfind ocamlc -where` and the `-I ${ocaml_stub_lib_path}` flag when compiling `z3native_stubs.o`. The new comment says ocamlc selects the matching runtime headers itself. This is a build-system change with no solver-semantics function to formalize.

## Obligations
- None were selected or checked.
- The change is not a solver function with branch guards or arithmetic edge cases, so it fits no bounded F* obligation.
- Re-verifying roughly 400 changed or added F* modules, and judging whether each is faithful to the C++ source, exceeds this run's bound of three functions and three obligations each.
- Status for every obligation: inconclusive (abstention). It is not evidence of safety, and no counterexample was found.

## Exclusions
- All 428 `fstar/` files: not re-verified, not compared against base, and not checked for admits or assumptions.
- Proof-module faithfulness to the C++ sources and the soundness of the new sort-indexed checker design.
- `src/api/ml/CMakeLists.txt`: reviewed by reading the patch only. Whether the OCaml header lookup works on every platform was not tested, and no PR code was run.

## Reproduction
A reviewer can run `/tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10` on individual PR modules in a fresh cache. This audit did not do so.