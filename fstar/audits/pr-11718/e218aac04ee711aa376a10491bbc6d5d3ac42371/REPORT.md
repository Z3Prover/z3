# F* audit, PR 11718 @ e218aac04ee711aa376a10491bbc6d5d3ac42371 (base f46b3c58e41c0f9531cbb7cbab243b8cd2a98250)

PR was open at this head; no prior `fstar-nfv-audit:<head-sha>` comment found.

## Scope
444 changed files: 443 under `fstar/` (new/modified F* proof modules, reports, CSV, PDF/TeX) and one production file, `src/api/ml/CMakeLists.txt`.

## Selected changed behavior: src/api/ml/CMakeLists.txt
The PR removes the `execute_process(ocamlfind ocamlc -where)` configure-time query and the `-I ${ocaml_stub_lib_path}` flag from the `z3native_stubs.o` custom command, relying on ocamlc to find runtime headers itself.
This is a build-system change with no solver logic, no branch guard, arithmetic or invariant. Nothing in the trusted F* semantics models CMake or OCaml toolchain include resolution, so no meaningful soundness obligation can be stated or mechanized. Whether `ocamlc -c` on a .c file finds `caml/*.h` without the explicit `-I` depends on the OCaml installation, so it needs a CI build with the OCaml bindings enabled. Not formally assessed.

## Excluded
All 443 `fstar/` files (proof modules, docs, CSV, PDF, TeX). Per audit rules, changed PR proof modules are not imported as trusted premises and PR code/scripts are not executed. Re-checking them is the job of the PR's own proof-checking CI; this audit did not check them. No proof modules were generated.

## Verdict: inconclusive
No obligation was formalized, no counterexample was found, nothing was proved. This is an abstention, not evidence of safety.
Tool versions: F* 2026.09.27; Z3 4.13.3 (pinned release backend). No F* verification invoked.
