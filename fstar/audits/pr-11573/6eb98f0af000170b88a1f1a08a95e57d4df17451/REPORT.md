# F* audit: PR #11573 fixed bv_family_id (head 6eb98f0af000170b88a1f1a08a95e57d4df17451, base 35cebef9e8899a1cabef8996f569a6e5fb9f9aa4)

Scope (partial): the PR changes ast.cpp (1 line), ast.h (1 line), bv_decl_plugin.cpp and bv_decl_plugin.h (mechanical replacement of get_fid()/m_afid by constant bv_family_id; bv_recognizers loses its fid constructor). Selected function: ast_manager::init (family-id assignment) with family_manager::mk_family_id (ast.cpp:127-137). Source read from PR diff plus base checkout; base ast.cpp lines 1313-1340.

Intended property: bv_family_id==7 equals the id the family manager actually assigns to "bv" in every ast_manager, so recognizers comparing against the constant agree with plugin-created terms.

Obligations (all proved in Z3BvFamilyId.fst):
1. O1: after the seven prior families, mk_family_id("bv") returns 7 (the new ENSURE succeeds).
2. O2: after init, lookup of "bv" yields 7 (bv_util, plugin registration, API m_bv_fid).
3. O3: mk_family_id never renumbers existing families (copy_families_plugins relies on stable ids).
4. O4 (extra): arith/polymorphic/user-sort remain 5/6/4, so no collision with 7.

Correspondence: family table = symbol_table + names vector; mk_family_id modelled as lookup-or-append. Assumptions: init runs the ENSUREs in the listed order at the start of every ast_manager constructor (all three constructors call init(), ast.cpp 1276/1291/1303, manually checked); no family is created before init (m_next_id starts at 0). Manual review only: the bv_decl_plugin.h/.cpp replacements of get_fid() by bv_bv_family_id were inspected from the diff, not formalized or mechanically checked per opcode. bv_util ctor still calls mk_family_id("bv"), now redundant but harmless. Residual risk: ENSURE is a runtime check.
Exclusions: C++ execution/memory safety, src/test/ast.cpp, individual opcode replacements in bv_decl_plugin.{cpp,h}, and any external user of the removed bv_recognizers(family_id) constructor (grep of base found only bv_util).
No counterexample found. Inherited assumptions: F* standard library only.

Reproduce (in a directory with Z3BvFamilyId.fst, fresh cache/out): timeout 120 /tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --z3rlimit 10 --cache_dir cache --odir out Z3BvFamilyId.fst
