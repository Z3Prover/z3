## Scope
Delta from audited 7303aad4 to 83abe3ec (base 59e40ee6): src/api/api_datatype.cpp Z3_query_constructor (lines ~262-300; head file sha256 efe7c457...cfafb), src/test/api.cpp (test rename only, excluded). Prior audit commits excluded.
## Obligations
- O1 proved: if num_fields > accessor count, error is set and nothing is written to constructor_decl/tester/accessors.
- O2 proved: if no error, all accessor indices i < num_fields are < accs.size().
- O3 proved: the previous ordering (check after ctor/tester writes) wrote outputs while reporting an error (witness nf=1, 0 accessors).
## Correspondence
Model result record = output writes; n = accs.size(). Pointer validity, get_constructor_accessors returning non-null, save_multiple_ast_trail and memory safety are manually reviewed only (note accs is dereferenced before the check; null for a non-constructor func_decl is not modeled).
## Assumptions
No axioms; only F* standard library.
## Exclusions
mk_to_fp_real unchanged since 7303aad4; src/test/api.cpp rename; src/test/fpa.cpp; fstar/audits files.
## Reproduce
fstar.exe --smt z3 --z3version 4.13.3 --z3rlimit 10 --cache_dir cache --odir out Pr11421QueryCtor.fst (F* 2026.09.27, Z3 4.13.3).