# F* audit, PR #11597 head b072c8390756f137e5449f9d775fc313dc4bb375 (base d86b80e7)

Partial scope. Audited 2 of 3 allowed changed functions, with 3 obligations on the first and 2 on the second:
1. `datatype::util::is_covariant(ast_mark&, ptr_vector<sort>&, sort*)` (src/ast/datatype_decl_plugin.cpp, hunk @@ -1051, new loop).
2. `theory_datatype::has_nested_datatype(sort*)` (src/smt/theory_datatype.cpp, new).

Obligations (all **proved**):
- Z3CovariantNested.o1: the iterative loop returns true iff no marked (being-defined) sort lies in a forbidden position. Forbidden positions are array domains at any nesting depth, and non-container, non-datatype array ranges.
- Z3CovariantNested.o3: a marked sort in an array domain forces rejection.
- Z3CovariantNested O2 `assert_norm` witnesses: Array(Int,Seq(Array(T,Int))) and the FSet variant are rejected, and Array(Int,Seq T) and Seq(Array(Int,T)) are accepted. These are positive/negative checks, not counterexamples.
- Z3NestedDatatypeSort.o1/o2: `has_nested` equals "peeling Array-range/Seq/FSet reaches a datatype".

No counterexample was found. Termination of the loop in is_covariant is mirrored by totality of `cov`.

Mapping and assumptions: sorts are modeled as an inductive tree. Multi-arity array domains and multiple sort parameters are folded into one. `get_subsorts` is modeled as transitive parameter closure. Mark state is a predicate `mk`. Inherited assumptions: F* core libraries only; no base modules imported.

Excluded and NOT audited: the `theory_datatype::get_nested_args` rewrite (enode root visited sets, array default and select parents, finite-set `in` literals, seq unit/concat), including conflict explanation completeness (m_used_eqs / new m_used_lits) and VERIFY(found) in occurs_check_explain; the `internalize` changes; `occurs_check` refactor; and the tests in src/test/parametric_datatype.cpp. Notably, conflict-explanation soundness of the new literals is manually reviewed only, not mechanized. Also unmodeled: C++ memory safety, enode/union-find dynamics, AST plumbing.

Source hashes: patch text of src/ast and src/smt files from the GitHub API sha256 b49aee2024dd85630a926f7749be6765abe698faca16c53da10db5d3f4c3e133. Tools: F* 2026.09.27, Z3 4.13.3 (pinned). Prior audits exist for earlier heads 1708eda2 and ba5474cd (different heads).

Reproduce: `fstar.exe --smt <z3-4.13.3> --z3version 4.13.3 --z3rlimit 10 --cache_dir C --odir O Z3CovariantNested.fst` (same for Z3NestedDatatypeSort.fst).
