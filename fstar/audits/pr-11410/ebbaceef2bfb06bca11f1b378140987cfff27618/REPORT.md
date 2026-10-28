# F* audit PR #11410 (head ebbaceef2bfb06bca11f1b378140987cfff27618, base 02f6a7e144ed5ce81ab07a1373fd667c60ead0c2)

Scope (partial): one changed function, `seq::monadic::parse_term` in `src/ast/seq/seq_monadic.cpp` (base sha256 89fcc330...bbe4, head sha256 232b8727...8d59; head lines ~119-144). Excluded: the new regression test `src/test/seq_monadic.cpp` (28 added lines), `seq_util::str::get_concat` itself beyond the model (unchanged, src/ast/seq_decl_plugin.cpp:965-980), memory/stack behavior, atom construction, `is_var`/`m.is_value` semantics.

Intended property: replacing recursive descent with `get_concat` flattening preserves the result and the atoms pushed (order, repeats, failure on unsupported leaves, including the atoms pushed before failure), while removing recursion depth.

Obligations (all **proved**):
1. `flat_spec`: worklist flattening (push e2 then e1, skip empty) equals ordered leaf flattening.
2. `old_eq_proc` (with `proc_append`): base recursive all_of-style parse equals leaf-wise processing of the flattening, incl. short-circuit.
3. `parse_equiv`: `new_parse t == old_parse t` for all trees.

Correspondence: tree = AST of concat/leaf; leaf_res models string/unit-of-value/var/reject/empty; atoms modeled by constructor tags. Assumptions: is_concat is a pure function of the node; get_concat's loop is as in the source (manually read, modeled, not mechanized from C++); leaf classification is the same predicate in both versions (verified by diff). Note: failure after partial atoms push is identical in both versions. The fix removes recursion in parse_term; stack safety of the iterative loop is not formally verified. Mechanized: semantic equivalence of the model only, not C++ execution.

Tools: F* 2026.09.27, Z3 4.13.3 (pinned release), z3rlimit 10, no admits/assumes. Inherits FStar standard library.

Command: timeout 120 /tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --cache_dir cache --odir out Pr11410ParseTerm.fst
