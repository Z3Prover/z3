# F* audit PR 11641 @ 0641a4e7706bb4e98ed1b52aacfd0484c3aa046e (base 1e136dcd)
Scope (partial): one changed function, `model_checker::assert_neg_q_m` in src/smt/smt_model_checker.cpp (new loop, patch lines ~212-231; base file sha256 e2b83d02259bb3b2d0301462626457bbfc5803ad703ee316c1a903d0823b3e44). Three obligations.
Excluded: test additions in src/test/smt_context.cpp (not semantic code), the include change, and all of MBQI/model evaluator/aux-context solving.

Guard: for each ground subterm t of sk_body with arith `is_considered_partially_interpreted` (div/idiv/mod/rem with non-numeral divisor), with a candidate-model interp of div0/idiv0/mod0, assert `(arg1 = 0) => t = interp(args)` in m_aux_context (within check()'s push scope).
Intended property: the aux solver's counterexample search is not given freedom to pick a div-by-zero value differing from the candidate model.
Obligations (all proved in MbqiDiv0Axiom.fst): O1 axiom holds for the candidate model's value (no genuine counterexample excluded); O2 with divisor 0 the axiom forces agreement with the model; O3 axiom vacuous when divisor nonzero.
Mapping: ints model values; f models fi->get_interp() substituted by args (var_subst std_order=false, var i -> arg i); sem_op models model semantics.
Assumptions/manual review (not mechanized): C++ execution, memory safety, that the evaluator leaves div unevaluated exactly when the model gives div0 semantics, that `rem` maps to mod0 as in base (model-side agreement for negative divisors not modelled), that arg(1) sort equals the numeral sort, Real vs Int sorts abstracted to int, skolem-containing terms included in `subterms::ground`. No counterexample found; no verdict on whole PR.
Commands: see log. F* 2026.09.27, Z3 4.13.3 (pinned).