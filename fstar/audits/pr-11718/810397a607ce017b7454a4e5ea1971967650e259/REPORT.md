## Scope
Head 810397a607ce017b7454a4e5ea1971967650e259, base f46b3c58e41c0f9531cbb7cbab243b8cd2a98250. Changed files: 439.

## Obligations
None selected: proved 0, counterexamples 0. Inconclusive by abstention.

Reasons:
- The only production-code change is src/api/ml/CMakeLists.txt, which removes the `ocamlc -where` execute_process and the `-I ${ocaml_stub_lib_path}` flag when building z3native_stubs.o (relying on ocamlc to select runtime headers). This is a build-system change with no function/branch-guard semantics to model in F*; the risk is build portability, which is manually reviewable only.
- fstar/cherry_runtime/main.cpp and tests.cpp are a new audit-tool runtime and Python tools under fstar/tools; they are not Z3 solver code. PR proof modules must not be trusted premises and were not executed (trusted-base rule), so their checking was not re-run.
- The bulk of PR is new F* proof modules and docs; auditing them would exceed the three-function/three-obligation bound.

## Exclusions
All 439 changed files are excluded from formal checking, including all fstar/*.fst, fstar/cherry_runtime/*.cpp, fstar/tools/*.py, docs and PDF, and src/api/ml/CMakeLists.txt (manual review only).

## Tooling
F* 2026.09.27 at /tmp/gh-aw/fstar/bin/fstar.exe; Z3 4.13.3 at /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3. No F* verification was invoked.

## Caveat
This is not evidence that the PR is safe; it is an explicit abstention. Semantic proofs would not mechanize C++ execution, memory safety, or the whole solver anyway.