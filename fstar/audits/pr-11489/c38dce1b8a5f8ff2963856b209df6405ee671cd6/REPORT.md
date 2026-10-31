# F* audit of PR 11489 @ c38dce1b8a5f8ff2963856b209df6405ee671cd6 (base deef01f5)

Scope (partial): one changed function, `datatype_factory::get_enumerator` (src/model/datatype_factory.cpp, head blob sha256 of decoded file f60e38fc3d1f7ec4999073098ee6cbea2ca30db76e83422a9cbae15d00ef2523, lines ~52-115). Excluded: comments/header edits, `datatype_factory.h` (comment-only), `src/test/model_retrieval.cpp` (tests), `get_fresh_value`, `term_enumeration`, performance claims, memory safety, AST plumbing.

Intended property: productions are registered only for datatype sorts in the recursive dependency group of s (reachable from s AND able to reach s), preserving mutual recursion including via sort parameters (Array/Seq).
Correspondence: sorts = nodes; edge(cur,arg) = `add_dependency` (constructor domain or `get_sort_parameters`); pass 1 = `reachable`; pass 2 = backward traversal over `parents`; `selected` = reach(s,x) /\ reach(x,s).

Obligations (all proved in DtEnumScope.fst):
- O1 root s is always selected: proved.
- O2 any two selected sorts are mutually dependent (group soundness): proved.
- O3 every sort on a cycle s->*x->*s is selected (mutual recursion/param paths preserved): proved.
- O4 refutation attempt/exclusion check: sort reachable from s but not reaching s is excluded (witness graph 0->1): proved consistent; no counterexample found.

Assumptions/manual review: graph model of C++ (no execution semantics); is_datatype filter and `get_datatype_constructors` assumed to be faithful; the `parents` map is assumed to record every edge (inspected: each edge goes through add_dependency). Residual manual observation: for non-recursive s `get_fresh_value` doesn't use this path; non-group datatype argument sorts are now supplied by `m_model.get_some_value` via external seeding (only for sorts appearing as production domains) - termination/completeness of that seeding not mechanized. Obligations are semantic, not verification of C++.

Reproduce: fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --cache_dir cache --odir out DtEnumScope.fst
