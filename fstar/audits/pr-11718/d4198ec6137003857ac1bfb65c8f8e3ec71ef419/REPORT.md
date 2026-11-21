## Scope
The PR changes 432 files. 431 are under fstar/ (F* proof modules and documentation). The only non-fstar change is src/api/ml/CMakeLists.txt, which drops the execute_process call to `ocamlfind ocamlc -where` and the corresponding `-I ${ocaml_stub_lib_path}` flag when compiling z3native_stubs.o, leaving header selection to ocamlc.

## Obligations
None selected. Changed F* proof modules are not trusted premises per workflow policy, and they are not changed C++ solver functions with branch guards. The CMake change is build plumbing with no solver semantics, so there is no meaningful F* model of it. Whether ocamlc's own include path suffices for OCaml runtime headers (caml/mlvalues.h) is a manual-review item.

## Exclusions
All 432 changed files are excluded from formal checking: the 3-function bound was not applicable because there are no changed C++ functions. Nothing here claims coverage of the PR.

## Tooling
F* 2026.09.27 at /tmp/gh-aw/fstar/bin/fstar.exe was present; no F* invocations were made, so no Z3 4.13.3 results exist. No proof modules are published.

## Verdict
Inconclusive: abstention, not evidence of safety. A semantic source audit is not mechanized verification of C++ execution.