# F* audit PR 11406 @ 4fb46f9f792c8205df4c669328b4b7be234eba70 (base 02f6a7e1)
Scope: 2 changed functions (Z3_apply_result_get_subgoal in src/api/api_tactic.cpp; Z3_query_constructor in src/api/api_datatype.cpp). src/test/api.cpp (tests) excluded. Not full PR coverage.
Source SHA256 (decoded, via contents API): api_tactic base 970052e3..., head a7a01c54...; api_datatype base 8b03b292..., head efe7c457...
## Obligations (all proved)
1. sub_sound: guard `i >= size` reject => accepted implies i < size (api_tactic.cpp ~L519).
2. sub_exact: rejection iff out of bounds (valid indices not rejected).
3. qc_sound: `num_fields > accs.size()` reject => each loop index i<num_fields is < accs.size() (api_datatype.cpp ~L280-285).
4. qc_partial / qc_zero: partial queries (nf<=arity) and zero-field constructors still accepted.
5. qc_atomic_reject: rejection happens before any output store (constructor_decl, tester, accessors), so outputs unchanged.
Base-version witnesses (assert-checked): size=0 or 3 with i=size passed old `i > size` guard yet out of bounds; arity 0 with num_fields=1 had no guard. These confirm the original bug, not a flaw in the head.
## Correspondence / assumptions
unsigned -> nat (no wraparound at these comparisons; both operands unsigned so comparison is exact). Vectors abstracted to lengths; ptr_vector operator[] reads in bounds iff index<size. get_constructor_accessors(f) assumed non-null for a datatype constructor (dereference not modeled; unchanged from base; the PR only moves this unconditional dereference earlier (base also dereferenced it before the loop), so nullness behavior is unchanged except ordering w.r.t. output stores). Caller-supplied `accessors` array capacity >= num_fields is an API precondition. Memory safety, C++ execution, and tests not mechanized. Only standard F* library assumed; no base fstar modules imported.
## Reproduce
timeout 120 /tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --include /home/runner/work/z3/z3/fstar --cache_dir cache --odir out Pr11406Bounds.fst
