/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    smt_params_helper.hpp

Abstract:

    Parameters for the 'smt' module.

--*/
#pragma once

#include "util/params.h"
#include "util/gparams.h"

#define SMT_PARAMS_HELPER_LIST(UINT_, BOOL_, DOUBLE_, STRING_, SYMBOL_) \
  BOOL_  (auto_config,                             "auto_config",                             true,                     "automatically configure solver") \
  SYMBOL_(logic,                                   "logic",                                   "",                       "logic used to setup the SMT solver") \
  UINT_  (random_seed,                             "random_seed",                             0,                        "random seed for the smt solver") \
  UINT_  (relevancy,                               "relevancy",                               2,                        "relevancy propagation heuristic: 0 - disabled, 1 - relevancy is tracked by only affects quantifier instantiation, 2 - relevancy is tracked, and an atom is only asserted if it is relevant") \
  BOOL_  (macro_finder,                            "macro_finder",                            false,                    "try to find universally quantified formulas that can be viewed as macros") \
  BOOL_  (quasi_macros,                            "quasi_macros",                            false,                    "try to find universally quantified formulas that are quasi-macros") \
  BOOL_  (restricted_quasi_macros,                 "restricted_quasi_macros",                 false,                    "try to find universally quantified formulas that are restricted quasi-macros") \
  BOOL_  (ematching,                               "ematching",                               true,                     "E-Matching based quantifier instantiation") \
  BOOL_  (ho_matching,                             "ho_matching",                             false,                    "higher-order matching for quantifier instantiation") \
  BOOL_  (ho_qmatcher,                             "ho_qmatcher",                             false,                    "higher-order matching and term-enumeration quantifier engine") \
  UINT_  (ho_matching_bound,                       "ho_matching_bound",                       10000,                    "per-problem expansion-step budget of the higher-order matching search; bounds the (undecidable) HO unification to guarantee termination") \
  BOOL_  (term_enumeration,                        "term_enumeration",                        false,                    "use term enumeration to populate instantiation sets for higher-order variables during model-based quantifier instantiation") \
  UINT_  (phase_selection,                         "phase_selection",                         3,                        "phase selection heuristic: 0 - always false, 1 - always true, 2 - phase caching, 3 - phase caching conservative, 4 - phase caching conservative 2, 5 - random, 6 - number of occurrences, 7 - theory") \
  UINT_  (phase_caching_on,                        "phase_caching_on",                        400,                      "number of conflicts while phase caching is on") \
  UINT_  (phase_caching_off,                       "phase_caching_off",                       100,                      "number of conflicts while phase caching is off") \
  UINT_  (restart_strategy,                        "restart_strategy",                        1,                        "0 - geometric, 1 - inner-outer-geometric, 2 - luby, 3 - fixed, 4 - arithmetic") \
  DOUBLE_(restart_factor,                          "restart_factor",                          1.1,                      "when using geometric (or inner-outer-geometric) progression of restarts, it specifies the constant used to multiply the current restart threshold") \
  UINT_  (case_split,                              "case_split",                              1,                        "0 - case split based on variable activity, 1 - similar to 0, but delay case splits created during the search, 2 - similar to 0, but cache the relevancy, 3 - case split based on relevancy (structural splitting), 4 - case split on relevancy and activity, 5 - case split on relevancy and current goal, 6 - activity-based case split with theory-aware branching activity") \
  BOOL_  (delay_units,                             "delay_units",                             false,                    "if true then z3 will not restart when a unit clause is learned") \
  UINT_  (delay_units_threshold,                   "delay_units_threshold",                   32,                       "maximum number of learned unit clauses before restarting, ignored if delay_units is false") \
  BOOL_  (elim_unconstrained,                      "elim_unconstrained",                      true,                     "pre-processing: eliminate unconstrained subterms") \
  BOOL_  (solve_eqs,                               "solve_eqs",                               true,                     "pre-processing: solve equalities") \
  BOOL_  (solve_eqs_non_ground,                    "solve_eqs.non_ground",                    true,                     "pre-processing: solve equalities. Allow eliminating variables by non-ground solutions which can break behavior for model evaluation.") \
  BOOL_  (solve_eqs_linear,                        "solve_eqs.linear",                        false,                    "allow only linear substitutions where a variable is replaced by a term having at most one non-constant argument") \
  BOOL_  (propagate_values,                        "propagate_values",                        true,                     "pre-processing: propagate values") \
  BOOL_  (bound_simplifier,                        "bound_simplifier",                        true,                     "apply bounds simplification during pre-processing") \
  BOOL_  (pull_nested_quantifiers,                 "pull_nested_quantifiers",                 false,                    "pre-processing: pull nested quantifiers") \
  BOOL_  (refine_inj_axioms,                       "refine_inj_axioms",                       true,                     "pre-processing: refine injectivity axioms") \
  BOOL_  (candidate_models,                        "candidate_models",                        false,                    "create candidate models even when quantifier or theory reasoning is incomplete") \
  UINT_  (max_conflicts,                           "max_conflicts",                           UINT_MAX,                 "maximum number of conflicts before giving up.") \
  UINT_  (restart_max,                             "restart.max",                             UINT_MAX,                 "maximal number of restarts.") \
  UINT_  (cube_depth,                              "cube_depth",                              1,                        "cube depth.") \
  UINT_  (threads,                                 "threads",                                 1,                        "maximal number of parallel threads.") \
  UINT_  (threads_max_conflicts,                   "threads.max_conflicts",                   400,                      "maximal number of conflicts between rounds of cubing for parallel SMT") \
  UINT_  (threads_cube_frequency,                  "threads.cube_frequency",                  2,                        "frequency for using cubing") \
  BOOL_  (mbqi,                                    "mbqi",                                    true,                     "model based quantifier instantiation (MBQI)") \
  UINT_  (mbqi_max_cexs,                           "mbqi.max_cexs",                           1,                        "initial maximal number of counterexamples used in MBQI, each counterexample generates a quantifier instantiation") \
  UINT_  (mbqi_max_cexs_incr,                      "mbqi.max_cexs_incr",                      0,                        "increment for MBQI_MAX_CEXS, the increment is performed after each round of MBQI") \
  UINT_  (mbqi_max_iterations,                     "mbqi.max_iterations",                     1000,                     "maximum number of rounds of MBQI") \
  BOOL_  (mbqi_trace,                              "mbqi.trace",                              false,                    "generate tracing messages for Model Based Quantifier Instantiation (MBQI). It will display a message before every round of MBQI, and the quantifiers that were not satisfied") \
  UINT_  (mbqi_force_template,                     "mbqi.force_template",                     10,                       "some quantifiers can be used as templates for building interpretations for functions. Z3 uses heuristics to decide whether a quantifier will be used as a template or not. Quantifiers with weight >= mbqi.force_template are forced to be used as a template") \
  STRING_(mbqi_id,                                 "mbqi.id",                                 "",                       "Only use model-based instantiation for quantifiers with id's beginning with string") \
  UINT_  (q_lift_ite,                              "q.lift_ite",                              0,                        "0 - don not lift non-ground if-then-else, 1 - use conservative ite lifting, 2 - use full lifting of if-then-else under quantifiers") \
  BOOL_  (q_lite,                                  "q.lite",                                  false,                    "Use cheap quantifier elimination during pre-processing") \
  BOOL_  (qi_profile,                              "qi.profile",                              false,                    "profile quantifier instantiation") \
  UINT_  (qi_profile_freq,                         "qi.profile_freq",                         UINT_MAX,                 "how frequent results are reported by qi.profile") \
  UINT_  (qi_max_instances,                        "qi.max_instances",                        UINT_MAX,                 "maximum number of quantifier instantiations") \
  DOUBLE_(qi_eager_threshold,                      "qi.eager_threshold",                      10.0,                     "threshold for eager quantifier instantiation") \
  DOUBLE_(qi_lazy_threshold,                       "qi.lazy_threshold",                       20.0,                     "threshold for lazy quantifier instantiation") \
  STRING_(qi_cost,                                 "qi.cost",                                 "(+ weight generation)",  "expression specifying what is the cost of a given quantifier instantiation") \
  UINT_  (qi_max_multi_patterns,                   "qi.max_multi_patterns",                   0,                        "specify the number of extra multi patterns") \
  UINT_  (qi_quick_checker,                        "qi.quick_checker",                        0,                        "specify quick checker mode, 0 - no quick checker, 1 - using unsat instances, 2 - using both unsat and no-sat instances") \
  BOOL_  (induction,                               "induction",                               false,                    "enable generation of induction lemmas") \
  BOOL_  (bv_reflect,                              "bv.reflect",                              true,                     "create enode for every bit-vector term") \
  BOOL_  (bv_enable_int2bv,                        "bv.enable_int2bv",                        true,                     "enable support for int2bv and bv2int operators") \
  BOOL_  (bv_watch_diseq,                          "bv.watch_diseq",                          false,                    "use watch lists instead of eager axioms for bit-vectors") \
  BOOL_  (bv_delay,                                "bv.delay",                                false,                    "delay internalize expensive bit-vector operations") \
  BOOL_  (bv_size_reduce,                          "bv.size_reduce",                          false,                    "pre-processing; turn assertions that set the upper bits of a bit-vector to constants into a substitution that replaces the bit-vector with constant bits. Useful for minimizing circuits as many input bits to circuits are constant") \
  UINT_  (bv_solver,                               "bv.solver",                               0,                        "bit-vector solver engine: 0 - bit-blasting, 1 - polysat, 2 - intblast, requires sat.smt=true") \
  BOOL_  (arith_random_initial_value,              "arith.random_initial_value",              false,                    "use random initial values in the simplex-based procedure for linear arithmetic") \
  UINT_  (arith_solver,                            "arith.solver",                            6,                        "arithmetic solver: 0 - no solver, 1 - bellman-ford based solver (diff. logic only), 2 - simplex based solver, 3 - floyd-warshall based solver (diff. logic only) and no theory combination 4 - utvpi, 5 - infinitary lra, 6 - lra solver") \
  BOOL_  (arith_nl,                                "arith.nl",                                true,                     "(incomplete) nonlinear arithmetic support based on Groebner basis and interval propagation, relevant only if smt.arith.solver=2") \
  BOOL_  (arith_nl_nra,                            "arith.nl.nra",                            true,                     "call nra_solver when incremental linearization does not produce a lemma, this option is ignored when arith.nl=false, relevant only if smt.arith.solver=6") \
  BOOL_  (arith_nl_nra_check_assignment,           "arith.nl.nra_check_assignment",           true,                     "call check_assignment in nra_solver to verify current assignment against nlsat constraints") \
  UINT_  (arith_nl_nra_check_assignment_max_fail,  "arith.nl.nra_check_assignment_max_fail",  7,                        "maximum consecutive check_assignment failures before disabling it") \
  BOOL_  (arith_nl_branching,                      "arith.nl.branching",                      true,                     "branching on integer variables in non linear clusters") \
  BOOL_  (arith_nl_expensive_patching,             "arith.nl.expensive_patching",             false,                    "use the expensive of monomials") \
  UINT_  (arith_nl_rounds,                         "arith.nl.rounds",                         1024,                     "threshold for number of (nested) final checks for non linear arithmetic, relevant only if smt.arith.solver=2") \
  BOOL_  (arith_nl_order,                          "arith.nl.order",                          true,                     "run order lemmas") \
  BOOL_  (arith_nl_order_binomial_sign,            "arith.nl.order.binomial_sign",            true,                     "run order_lemma_on_binomial_sign; disabling it keeps the structural order-lemma splitting") \
  BOOL_  (arith_nl_expp,                           "arith.nl.expp",                           false,                    "expensive patching") \
  BOOL_  (arith_nl_tangents,                       "arith.nl.tangents",                       true,                     "run tangent lemmas") \
  BOOL_  (arith_nl_tangents_box_corners,           "arith.nl.tangents.box_corners",           false,                    "choose tangent-plane points at the bound-box corners instead of the model-centered val(x) +/- delta; produces the McCormick under/over envelope and is deterministic and snapshot-independent") \
  BOOL_  (arith_nl_horner,                         "arith.nl.horner",                         true,                     "run horner's heuristic") \
  UINT_  (arith_nl_horner_subs_fixed,              "arith.nl.horner_subs_fixed",              2,                        "0 - no subs, 1 - substitute, 2 - substitute fixed zeros only") \
  UINT_  (arith_nl_horner_frequency,               "arith.nl.horner_frequency",               4,                        "horner's call frequency") \
  UINT_  (arith_nl_horner_row_length_limit,        "arith.nl.horner_row_length_limit",        10,                       "row is disregarded by the heuristic if its length is longer than the value") \
  UINT_  (arith_nl_grobner_row_length_limit,       "arith.nl.grobner_row_length_limit",       10,                       "row is disregarded by the heuristic if its length is longer than the value") \
  UINT_  (arith_nl_grobner_frequency,              "arith.nl.grobner_frequency",              4,                        "grobner's call frequency") \
  BOOL_  (arith_nl_grobner,                        "arith.nl.grobner",                        true,                     "run grobner's basis heuristic") \
  UINT_  (arith_nl_grobner_eqs_growth,             "arith.nl.grobner_eqs_growth",             10,                       "grobner's number of equalities growth ") \
  UINT_  (arith_nl_grobner_expr_size_growth,       "arith.nl.grobner_expr_size_growth",       2,                        "grobner's maximum expr size growth") \
  UINT_  (arith_nl_grobner_expr_degree_growth,     "arith.nl.grobner_expr_degree_growth",     2,                        "grobner's maximum expr degree growth") \
  UINT_  (arith_nl_grobner_max_simplified,         "arith.nl.grobner_max_simplified",         10000,                    "grobner's maximum number of simplifications") \
  UINT_  (arith_nl_grobner_cnfl_to_report,         "arith.nl.grobner_cnfl_to_report",         1,                        "grobner's maximum number of conflicts to report") \
  BOOL_  (arith_nl_grobner_propagate_quotients,    "arith.nl.grobner_propagate_quotients",    true,                     "detect conflicts x*y + z = 0 where x doesn't divide z") \
  BOOL_  (arith_nl_grobner_gcd_test,               "arith.nl.grobner_gcd_test",               true,                     "detect gcd conflicts for polynomial powers x^k - y = 0") \
  BOOL_  (arith_nl_grobner_exp_delay,              "arith.nl.grobner_exp_delay",              true,                     "use exponential delay between grobner basis attempts") \
  BOOL_  (arith_nl_grobner_adaptive,               "arith.nl.grobner_adaptive",               false,                    "scale grobner growth knobs (eqs/size/degree/max_simplified) up on productive runs and down on misses") \
  UINT_  (arith_nl_gr_q,                           "arith.nl.gr_q",                           10,                       "grobner's quota") \
  UINT_  (arith_nl_grobner_subs_fixed,             "arith.nl.grobner_subs_fixed",             1,                        "0 - no subs, 1 - substitute, 2 - substitute fixed zeros only") \
  BOOL_  (arith_nl_grobner_expand_terms,           "arith.nl.grobner_expand_terms",           true,                     "expand terms before computing grobner basis") \
  BOOL_  (arith_nl_grobner_perfect_squares,        "arith.nl.grobner_perfect_squares",        true,                     "expand perfect squares with Grobner") \
  BOOL_  (arith_nl_monomial_sandwich,              "arith.nl.monomial_sandwich",              false,                    "derive bound on a monomial factor by pairing two LP rows that share the other factor") \
  UINT_  (arith_nl_monomial_sandwich_max_fanout,   "arith.nl.monomial_sandwich.max_fanout",   0,                        "skip monomial sandwich when the conclusion factor appears in more than this many monomials (0 = no limit)") \
  BOOL_  (arith_nl_monomial_binomial_sign,         "arith.nl.monomial_binomial_sign",         false,                    "derive bound on a binomial-monomial factor anchored on the current LP value of the monomial; replaces order_lemma_on_binomial_sign with a deterministic factor bound conditioned on a one-sided snapshot of the monomial value") \
  BOOL_  (arith_nl_reduce_pseudo_linear,           "arith.nl.reduce_pseudo_linear",           true,                     "create incremental linearization axioms for pseudo-linear monomials") \
  UINT_  (arith_nl_delay,                          "arith.nl.delay",                          10,                       "number of calls to final check before invoking bounded nlsat check") \
  BOOL_  (arith_nl_propagate_linear_monomials,     "arith.nl.propagate_linear_monomials",     true,                     "propagate linear monomials") \
  BOOL_  (arith_nl_linearize_violated_monomials,   "arith.nl.linearize_violated_monomials",   true,                     "in final check, install the defining row m = k*w for violated monomials with at most one non-fixed factor before resorting to case splits and horner/grobner") \
  BOOL_  (arith_nl_optimize_bounds,                "arith.nl.optimize_bounds",                true,                     "enable bounds optimization") \
  UINT_  (arith_nl_optimize_bounds_lp_max_vars,    "arith.nl.optimize_bounds_lp_max_vars",    120,                      "skip LP-based nonlinear bounds optimization when the number of candidate monomial variables exceeds this threshold (0 = unlimited)") \
  BOOL_  (arith_nl_cross_nested,                   "arith.nl.cross_nested",                   true,                     "enable cross-nested consistency checking") \
  BOOL_  (arith_nl_log,                            "arith.nl.log",                            false,                    "Log lemmas sent to nra solver") \
  BOOL_  (arith_propagate_eqs,                     "arith.propagate_eqs",                     true,                     "propagate (cheap) equalities") \
  DOUBLE_(arith_epsilon,                           "arith.epsilon",                           1.0,                      "initial value of epsilon used for model generation of infinitesimals") \
  UINT_  (arith_propagation_mode,                  "arith.propagation_mode",                  1,                        "0 - no propagation, 1 - propagate existing literals, 2 - refine finite bounds") \
  UINT_  (arith_branch_cut_ratio,                  "arith.branch_cut_ratio",                  2,                        "branch/cut ratio for linear integer arithmetic") \
  BOOL_  (arith_int_eq_branch,                     "arith.int_eq_branch",                     false,                    "branching using derived integer equations") \
  BOOL_  (arith_ignore_int,                        "arith.ignore_int",                        false,                    "treat integer variables as real") \
  BOOL_  (arith_dump_lemmas,                       "arith.dump_lemmas",                       false,                    "dump arithmetic theory lemmas to files") \
  BOOL_  (arith_dump_bound_lemmas,                 "arith.dump_bound_lemmas",                 false,                    "dump linear solver bounds to files in smt2 format") \
  BOOL_  (arith_greatest_error_pivot,              "arith.greatest_error_pivot",              false,                    "Pivoting strategy") \
  BOOL_  (arith_eager_eq_axioms,                   "arith.eager_eq_axioms",                   true,                     "eager equality axioms") \
  BOOL_  (arith_auto_config_simplex,               "arith.auto_config_simplex",               false,                    "force simplex solver in auto_config") \
  UINT_  (arith_rep_freq,                          "arith.rep_freq",                          0,                        "the report frequency, in how many iterations print the cost and other info") \
  BOOL_  (arith_min,                               "arith.min",                               false,                    "minimize cost") \
  BOOL_  (arith_print_stats,                       "arith.print_stats",                       false,                    "print statistic") \
  BOOL_  (arith_validate,                          "arith.validate",                          false,                    "validate lemmas generated by arithmetic solver") \
  UINT_  (arith_simplex_strategy,                  "arith.simplex_strategy",                  0,                        "simplex strategy for the solver") \
  BOOL_  (arith_enable_hnf,                        "arith.enable_hnf",                        true,                     "enable hnf (Hermite Normal Form) cuts") \
  BOOL_  (arith_bprop_on_pivoted_rows,             "arith.bprop_on_pivoted_rows",             true,                     "propagate bounds on rows changed by the pivot operation") \
  BOOL_  (arith_print_ext_var_names,               "arith.print_ext_var_names",               false,                    "print external variable names") \
  UINT_  (pb_conflict_frequency,                   "pb.conflict_frequency",                   1000,                     "conflict frequency for Pseudo-Boolean theory") \
  BOOL_  (pb_learn_complements,                    "pb.learn_complements",                    true,                     "learn complement literals for Pseudo-Boolean theory") \
  BOOL_  (up_persist_clauses,                      "up.persist_clauses",                      false,                    "replay propagated clauses below the levels they are asserted") \
  BOOL_  (array_weak,                              "array.weak",                              false,                    "weak array theory") \
  BOOL_  (array_extensional,                       "array.extensional",                       true,                     "extensional array theory") \
  BOOL_  (clause_proof,                            "clause_proof",                            false,                    "record a clausal proof") \
  UINT_  (dack,                                    "dack",                                    1,                        "0 - disable dynamic ackermannization, 1 - expand Leibniz's axiom if a congruence is the root of a conflict, 2 - expand Leibniz's axiom if a congruence is used during conflict resolution") \
  BOOL_  (dack_eq,                                 "dack.eq",                                 false,                    "enable dynamic ackermannization for transitivity of equalities") \
  DOUBLE_(dack_factor,                             "dack.factor",                             0.1,                      "number of instance per conflict") \
  UINT_  (dack_gc,                                 "dack.gc",                                 2000,                     "Dynamic ackermannization garbage collection frequency (per conflict)") \
  DOUBLE_(dack_gc_inv_decay,                       "dack.gc_inv_decay",                       0.8,                      "Dynamic ackermannization garbage collection decay") \
  UINT_  (dack_threshold,                          "dack.threshold",                          10,                       " number of times the congruence rule must be used before Leibniz's axiom is expanded") \
  BOOL_  (theory_case_split,                       "theory_case_split",                       false,                    "Allow the context to use heuristics involving theory case splits, which are a set of literals of which exactly one can be assigned True. If this option is false, the context will generate extra axioms to enforce this instead.") \
  SYMBOL_(string_solver,                           "string_solver",                           "seq",                    "solver for string/sequence theories. options are: 'z3str3' (specialized string solver), 'seq' (sequence solver), 'auto' (use static features to choose best solver), 'empty' (a no-op solver that forces an answer unknown if strings were used), 'none' (no solver)") \
  BOOL_  (core_validate,                           "core.validate",                           false,                    "[internal] validate unsat core produced by SMT context. This option is intended for debugging") \
  UINT_  (seq_parikh_k,                            "seq.parikh_k",                            0,                        "maximal factor length of the Parikh abstraction over word equations. 1 counts single characters, 2 also counts adjacent pairs. 0 disables the abstraction. Values above 2 are clamped to 2") \
  UINT_  (seq_parikh_n,                            "seq.parikh_n",                            2,                        "maximal modulus the Parikh abstraction over word equations uses to separate positions by their residue. 1 ignores positions") \
  UINT_  (seq_parikh_chars,                        "seq.parikh_chars",                        6,                        "how many distinct characters the Parikh abstraction keeps apart. The remaining characters share one class") \
  BOOL_  (seq_split_w_len,                         "seq.split_w_len",                         true,                     "enable splitting guided by length constraints") \
  BOOL_  (seq_validate,                            "seq.validate",                            false,                    "enable self-validation of theory axioms created by seq theory") \
  BOOL_  (seq_regex_monadic,                       "seq.regex_monadic",                       true,                     "use the monadic regular-expression end-game solver") \
  UINT_  (seq_regex_budget,                        "seq.regex_budget",                        1000000,                  "work budget (search nodes and product expansions) for a single decision of the monadic regular-expression solver, after which it gives up. A budget of 0 makes it give up immediately") \
  SYMBOL_(seq_regex_transition_mode,               "seq.regex_transition_mode",               "light-ant",              "transition mode of the monadic regular-expression solver. options are: 'light-ant' (split derivative targets over top-level unions), 'brz' (keep derivative targets in Brzozowski normal form)") \
  SYMBOL_(seq_regex_orientation,                   "seq.regex_orientation",                   "retry",                  "direction the monadic regular-expression solver reads memberships in. options are: 'forward', 'reversed' (solve rev(t) in rev(R), which is equisatisfiable and can have a far smaller derivative automaton), 'retry' (read forwards and, if the search runs out of budget, read the same decision backwards)") \
  UINT_  (seq_regex_split,                         "seq.regex_split",                         10,                       "maximum refinement rounds the monadic regular-expression solver spends decomposing a membership in an intersection of regexes, once reading the decision in both directions has run out of budget. Each round decides a relaxation that keeps only some of the intersected regexes: a relaxation that is unsatisfiable refutes the original, and a model accepted by every dropped regex satisfies it. 0 disables the decomposition") \
  UINT_  (seq_max_unfolding,                       "seq.max_unfolding",                       1000000000,               "maximal unfolding depth for checking string equations and regular expressions") \
  UINT_  (seq_min_unfolding,                       "seq.min_unfolding",                       1,                        "initial bound for strings whose lengths are bounded by iterative deepening. Set this to a higher value if there are only models with larger string lengths") \
  BOOL_  (theory_aware_branching,                  "theory_aware_branching",                  false,                    "Allow the context to use extra information from theory solvers regarding literal branching prioritization.") \
  BOOL_  (sls_enable,                              "sls.enable",                              false,                    "enable sls co-processor with SMT engine") \
  BOOL_  (sls_parallel,                            "sls.parallel",                            true,                     "use sls co-processor in parallel or sequential with SMT engine") \
  BOOL_  (core_minimize,                           "core.minimize",                           false,                    "minimize unsat core produced by SMT context") \
  BOOL_  (core_extend_patterns,                    "core.extend_patterns",                    false,                    "extend unsat core with literals that trigger (potential) quantifier instances") \
  UINT_  (core_extend_patterns_max_distance,       "core.extend_patterns.max_distance",       UINT_MAX,                 "limits the distance of a pattern-extended unsat core") \
  BOOL_  (core_extend_nonlocal_patterns,           "core.extend_nonlocal_patterns",           false,                    "extend unsat cores with literals that have quantifiers with patterns that contain symbols which are not in the quantifier's body") \
  UINT_  (lemma_gc_strategy,                       "lemma_gc_strategy",                       0,                        "lemma garbage collection strategy: 0 - fixed, 1 - geometric, 2 - at restart, 3 - none") \
  UINT_  (dt_lazy_splits,                          "dt_lazy_splits",                          1,                        "How lazy datatype splits are performed: 0- eager, 1- lazy for infinite types, 2- lazy") \
  BOOL_  (qsat_use_qel,                            "qsat_use_qel",                            true,                     "Use QEL for lite quantifier elimination and model-based projection in QSAT")

Z3_DEFINE_MODULE_PARAMS(smt_params_helper, "smt", SMT_PARAMS_HELPER_LIST);

/*
   REG_MODULE_PARAMS('smt', 'smt_params_helper::collect_param_descrs')
   REG_MODULE_DESCRIPTION('smt', 'smt solver based on lazy smt')
*/

#undef SMT_PARAMS_HELPER_LIST
