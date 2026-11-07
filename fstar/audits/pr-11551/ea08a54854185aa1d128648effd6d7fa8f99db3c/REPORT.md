# F* audit PR #11551 @ ea08a54854185aa1d128648effd6d7fa8f99db3c (base 684853cb1545622a353660d5de601032f060ffb1)

Source: src/ast/ast_smt2_pp.cpp (patch hunks read via contents/PR files API; not executed).
Tools: F* 2026.09.27, Z3 4.13.3 (pinned release backend), --z3rlimit 10, 120s timeout, fresh cache.

## Changed functions in scope (3)
1. smt2_pp_environment::pp_fdecl_name: internal BV div/rem ops (OP_BSDIV_I, BUDIV_I, BSREM_I, BUREM_I, BSMOD_I) print as bvsdiv/bvudiv/bvsrem/bvurem/bvsmod.
2. smt2_printer::flat_assoc: never flattens bv concat.
3. smt2_printer concat branch (n>2 args): prints left-nested binary (concat (concat a b) c)...

## Obligations
- A (proved): left fold of binary concat equals positional n-ary concat value: foldl_cat acc xs = acc*2^W + nary xs (fold_correct). Concat is associative, so the printed form is semantically equal.
- B (proved): leaf order/multiplicity preserved by the left-nested tree (leaves_fold).
- C (proved): the five renamed operators map to pairwise distinct standard names (name_inj).

## Correspondence / assumptions
- Values modeled as naturals with widths; modular wrap not needed since concat widths sum exactly. Format construction (mk_compose/mk_group), iterator handling, and the it/end ranges are modeled as an abstract list fold, not verified in C++.
- Semantic equivalence of internal *_I operators to the named SMT-LIB ops (including division by zero) is NOT proved; only name distinctness. That the _I ops' semantics match the standard names is manually reviewed/assumed from existing Z3 design.
- Case n==2 falls through to the existing path (unchanged); flat_assoc early-return for concat only disables flattening (conservative).
- Standard F* library only; no admits/assumes/axioms.

## Exclusions
src/test/smt2print_parse.cpp (tests), the bv_decl_plugin.h include, memory safety/AST plumbing, parser round trip, and the rest of the printer.

## Result
No counterexample; selected model-level obligations proved. Not mechanized C++ verification.

## Reproduce
cd /tmp/gh-aw/agent/fstar-audit; fstar.exe --smt (z3-4.13.3) --z3version 4.13.3 --z3rlimit 10 --cache_dir cache --odir out Pr11551Concat.fst
