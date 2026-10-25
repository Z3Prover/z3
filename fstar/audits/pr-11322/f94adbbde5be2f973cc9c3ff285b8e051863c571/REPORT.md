# PR 11322 audit at f94adbbde5be2f973cc9c3ff285b8e051863c571 (base 2203323af22963b7db16a308a20ce5eded3c30ef)

Scope: one changed function, `theory_array_full::assert_lambda_congruence` (src/smt/theory_array_full.cpp, new, called from final_check_eh when r == FC_DONE). Head differs from the previously audited 9e53f4bc only by a merge of master (tests/audit files/other base changes); the C++ function is the same as audited.

Obligations (all proved in Z3Pr11322LambdaCongruenceHead.fst):
1. o1: the congruence axiom queued by assert_congruent (a = b ==> forall i. a[i] = b[i]) is valid in functional array semantics.
2. o2: pairs (root, class member) drawn from one equivalence class yield valid axioms.
3. o3/o3b: for #11267 (store(lambda x.x,7,0) = store(const 3,7,0)) the axiom at index 8 gives 8 = 3, so unsat; where a store overwrites the only difference, the stores agree pointwise so no spurious conflict.

Correspondence: arrays are int->int functions; enode equivalence classes are equalities; the root->parent traversal is abstracted (only soundness of axioms and refutation power are shown).
Assumptions: F* standard library; Z3 4.13.3 backend. Fingerprint dedup and can_propagate are assumed to behave as in the base.
Excluded: termination of the worklist, relevancy filtering (is_relevant), tests in src/test/smt_context.cpp, header, array_fake_support early return, completeness for other shapes, C++ memory safety and execution. Not mechanized C++ verification.
Versions: F* 2026.09.27; Z3 4.13.3.
Reproduce: fstar.exe --smt (z3) --z3version 4.13.3 --z3rlimit 10 --cache_dir cache --odir out --include fstar Z3Pr11322LambdaCongruenceHead.fst
