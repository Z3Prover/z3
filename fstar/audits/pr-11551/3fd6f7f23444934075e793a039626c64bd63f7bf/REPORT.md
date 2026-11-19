# F* audit PR 11551 @ 3fd6f7f23444934075e793a039626c64bd63f7bf (base 814fda3f)
Scope (partial): src/ast/ast_smt2_pp.cpp `smt2_printer::process_app` n-ary bv concat branch (guard `is_app_of(t,bv_family_id,OP_CONCAT) && num_args>2`).
Excluded: `smt2_pp_environment::pp_fdecl_name` *_I rename (only name-mapping reviewed manually, not mechanized), src/test/smt2print_parse.cpp, fstar/audits artifacts, C++ execution/memory safety/format AST plumbing.
Obligations (all proved, model level): O1 binary concat preserves BV well-formedness; O2 left-fold of binary concat equals right-nested n-ary concat (value and width); O3 leaf order/multiplicity preserved and the two initial iterator reads are valid under num_args>2.
Assumptions: nat values with widths as in bv_decl_plugin concat semantics (high operand first); children printed by existing code are correct; FStar.Math.Lemmas/List.Tot.Properties from the standard library. No base fstar modules used. No admit/assume.
Counterexample search: none found; none expected from the model.
Reproduce: see verification log; F* 2026.09.27, Z3 4.13.3 (pinned release).
Not proved: that internal *_I division ops are semantically equal to the named SMT-LIB ops (the printer renames them; this is intentional printing of an internal op as standard name).
