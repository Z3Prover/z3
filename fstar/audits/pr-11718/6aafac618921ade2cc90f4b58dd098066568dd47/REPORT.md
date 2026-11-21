# F* audit, PR #11718 at 6aafac618921ade2cc90f4b58dd098066568dd47 (base f46b3c58e41c0f9531cbb7cbab243b8cd2a98250)

Checks: PR open at this SHA; no existing fstar-nfv-audit:(sha) comment found.

## Changed production code
- src/api/ml/CMakeLists.txt: removes the execute_process call that ran `ocamlfind ocamlc -where`, and drops `-I ${ocaml_stub_lib_path}` from the z3native_stubs.o compile command. The comment says ocamlc will select runtime headers itself.
- This is build plumbing, not solver semantics. There are no C++ functions, soundness guards, or arithmetic edge cases to model.

## Obligations
None attempted. Status: inconclusive (nothing selected for proof).
Reason: the change has no semantic property expressible in F*. Whether `ocamlc -c` finds caml headers without the explicit -I depends on the OCaml toolchain, which only a build check can confirm. That build check was not run, because PR code and builds must not be executed.

## Exclusions (not audited)
- All 449 fstar/ files (new proof modules, checkers, reports, CSV, PDF). Changed PR proof modules must not be imported as trusted premises, and the bounded budget (three functions) does not cover a checker of this size. Their proof-checking status is not claimed.
- The semantic correspondence of the independent checker to Z3 proof rules was not reviewed.

## Tool versions (trusted base)
F* 2026.09.27; Z3 4.13.3 (pinned release backend). No verification invocations were made, so there are no stdout/stderr logs.

## Not covered
Semantic proofs would not mechanize C++ execution, memory safety, or the whole solver in any case.
