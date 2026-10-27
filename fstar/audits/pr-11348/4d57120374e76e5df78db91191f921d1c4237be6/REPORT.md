## Scope
Function: set_option_cmd::set for :global-declarations (src/cmd_context/basic_cmds.cpp, hunk ``@523-531``) at head 4d57120. Base 9dbe8c8.

## Obligations (all proved)
1. SASSERT(!has_manager()) in set_global_decls is unreachable: set_global_decls is only called when value differs from the current one, and then check_not_initialized throws if a manager exists.
2. Changing the value after init still throws (as base).
3. Before init, behavior matches base (set, or no-op when equal).

## Assumptions
set_global_decls has SASSERT(!has_manager()) and check_not_initialized throws iff has_manager (taken from the previous audit and base code; not re-fetched line by line). F* standard library and Z3 4.13.3 backend trusted. F* 2026.09.27.

## Correspondence
Boolean abstraction of ctx state; not a mechanization of C++ execution, memory safety, or exceptions plumbing.

## Exclusions
All other changed files, including Z3IntegerDivision.fst lemma_upper_bound/lemma_residual_bound/lemma_int_inequality, Z3ArrayEquality, Z3SortedQuantifier, tooling, and the OCaml checker, were not audited (proof modules are checked by their own F* build).

## Reproduce
`cd dir; mkdir cache out; see verification_log`.