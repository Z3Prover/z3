/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    fp_params.hpp

Abstract:

    Parameters for the 'fp' module.

--*/
#pragma once

#include "util/params.h"
#include "util/gparams.h"

#define FP_PARAMS_LIST(UINT_, BOOL_, DOUBLE_, STRING_, SYMBOL_) \
  SYMBOL_(engine,                                       "engine",                                       "auto-config",  "Select: auto-config, datalog, bmc, spacer") \
  UINT_  (rlimit,                                       "rlimit",                                       0,              "deterministic resource limit (0 means no limit)") \
  SYMBOL_(datalog_default_table,                        "datalog.default_table",                        "sparse",       "default table implementation: sparse, hashtable, bitvector, interval") \
  SYMBOL_(datalog_default_relation,                     "datalog.default_relation",                     "pentagon",     "default relation implementation: external_relation, pentagon") \
  BOOL_  (datalog_generate_explanations,                "datalog.generate_explanations",                false,          "produce explanations for produced facts when using the datalog engine") \
  BOOL_  (datalog_use_map_names,                        "datalog.use_map_names",                        true,           "use names from map files when displaying tuples") \
  BOOL_  (datalog_magic_sets_for_queries,               "datalog.magic_sets_for_queries",               false,          "magic set transformation will be used for queries") \
  BOOL_  (datalog_explanations_on_relation_level,       "datalog.explanations_on_relation_level",       false,          "if true, explanations are generated as history of each relation, rather than per fact (generate_explanations must be set to true for this option to have any effect)") \
  BOOL_  (datalog_unbound_compressor,                   "datalog.unbound_compressor",                   true,           "auxiliary relations will be introduced to avoid unbound variables in rule heads") \
  BOOL_  (datalog_similarity_compressor,                "datalog.similarity_compressor",                true,           "rules that differ only in values of constants will be merged into a single rule") \
  UINT_  (datalog_similarity_compressor_threshold,      "datalog.similarity_compressor_threshold",      11,             "if similarity_compressor is on, this value determines how many similar rules there must be in order for them to be merged") \
  BOOL_  (datalog_all_or_nothing_deltas,                "datalog.all_or_nothing_deltas",                false,          "compile rules so that it is enough for the delta relation in union and widening operations to determine only whether the updated relation was modified or not") \
  BOOL_  (datalog_compile_with_widening,                "datalog.compile_with_widening",                false,          "widening will be used to compile recursive rules") \
  BOOL_  (datalog_default_table_checked,                "datalog.default_table_checked",                false,          "if true, the default table will be default_table inside a wrapper that checks that its results are the same as of default_table_checker table") \
  SYMBOL_(datalog_default_table_checker,                "datalog.default_table_checker",                "null",         "see default_table_checked") \
  SYMBOL_(datalog_check_relation,                       "datalog.check_relation",                       "null",         "name of default relation to check. operations on the default relation will be verified using SMT solving") \
  UINT_  (datalog_initial_restart_timeout,              "datalog.initial_restart_timeout",              0,              "length of saturation run before the first restart (in ms), zero means no restarts") \
  UINT_  (datalog_timeout,                              "datalog.timeout",                              0,              "Time limit used for saturation") \
  BOOL_  (datalog_output_profile,                       "datalog.output_profile",                       false,          "determines whether profile information should be output when outputting Datalog rules or instructions") \
  BOOL_  (datalog_print_tuples,                         "datalog.print.tuples",                         true,           "determines whether tuples for output predicates should be output") \
  UINT_  (datalog_profile_timeout_milliseconds,         "datalog.profile_timeout_milliseconds",         0,              "instructions and rules that took less than the threshold will not be printed when printed the instruction/rule list") \
  BOOL_  (datalog_dbg_fpr_nonempty_relation_signature,  "datalog.dbg_fpr_nonempty_relation_signature",  false,          "if true, finite_product_relation will attempt to avoid creating inner relation with empty signature by putting in half of the table columns, if it would have been empty otherwise") \
  BOOL_  (datalog_subsumption,                          "datalog.subsumption",                          true,           "if true, removes/filters predicates with total transitions") \
  BOOL_  (generate_proof_trace,                         "generate_proof_trace",                         false,          "trace for 'sat' answer as proof object") \
  BOOL_  (spacer_push_pob,                              "spacer.push_pob",                              false,          "push blocked pobs to higher level") \
  UINT_  (spacer_push_pob_max_depth,                    "spacer.push_pob_max_depth",                    UINT_MAX,       "Maximum depth at which push_pob is enabled") \
  BOOL_  (validate,                                     "validate",                                     false,          "validate result (by proof checking or model checking)") \
  BOOL_  (spacer_simplify_lemmas_pre,                   "spacer.simplify_lemmas_pre",                   false,          "simplify derived lemmas before inductive propagation") \
  BOOL_  (spacer_simplify_lemmas_post,                  "spacer.simplify_lemmas_post",                  false,          "simplify derived lemmas after inductive propagation") \
  BOOL_  (spacer_use_inductive_generalizer,             "spacer.use_inductive_generalizer",             true,           "generalize lemmas using induction strengthening") \
  UINT_  (spacer_max_num_contexts,                      "spacer.max_num_contexts",                      500,            "maximal number of contexts to create") \
  BOOL_  (print_fixedpoint_extensions,                  "print_fixedpoint_extensions",                  true,           "use SMT-LIB2 fixedpoint extensions, instead of pure SMT2, when printing rules") \
  BOOL_  (print_low_level_smt2,                         "print_low_level_smt2",                         false,          "use (faster) low-level SMT2 printer (the printer is scalable but the result may not be as readable)") \
  BOOL_  (print_with_variable_declarations,             "print_with_variable_declarations",             true,           "use variable declarations when displaying rules (instead of attempting to use original names)") \
  BOOL_  (print_answer,                                 "print_answer",                                 false,          "print answer instance(s) to query") \
  BOOL_  (print_certificate,                            "print_certificate",                            false,          "print certificate for reachability or non-reachability") \
  BOOL_  (print_boogie_certificate,                     "print_boogie_certificate",                     false,          "print certificate for reachability or non-reachability using a format understood by Boogie") \
  SYMBOL_(print_aig,                                    "print_aig",                                    "",             "Dump clauses in AIG text format (AAG) to the given file name") \
  BOOL_  (print_statistics,                             "print_statistics",                             false,          "print statistics") \
  SYMBOL_(tab_selection,                                "tab.selection",                                "weight",       "selection method for tabular strategy: weight (default), first, var-use") \
  BOOL_  (xform_bit_blast,                              "xform.bit_blast",                              false,          "bit-blast bit-vectors") \
  BOOL_  (xform_magic,                                  "xform.magic",                                  false,          "perform symbolic magic set transformation") \
  BOOL_  (xform_scale,                                  "xform.scale",                                  false,          "add scaling variable to linear real arithmetic clauses") \
  BOOL_  (xform_inline_linear,                          "xform.inline_linear",                          true,           "try linear inlining method") \
  BOOL_  (xform_inline_eager,                           "xform.inline_eager",                           true,           "try eager inlining of rules") \
  BOOL_  (xform_inline_linear_branch,                   "xform.inline_linear_branch",                   false,          "try linear inlining method with potential expansion") \
  BOOL_  (xform_compress_unbound,                       "xform.compress_unbound",                       true,           "compress tails with unbound variables") \
  BOOL_  (xform_fix_unbound_vars,                       "xform.fix_unbound_vars",                       false,          "fix unbound variables in tail") \
  UINT_  (xform_unfold_rules,                           "xform.unfold_rules",                           0,              "unfold rules statically using iterative squaring") \
  BOOL_  (xform_slice,                                  "xform.slice",                                  true,           "simplify clause set using slicing") \
  BOOL_  (spacer_use_euf_gen,                           "spacer.use_euf_gen",                           false,          "Generalize lemmas and pobs using implied equalities") \
  BOOL_  (xform_transform_arrays,                       "xform.transform_arrays",                       false,          "Rewrites arrays equalities and applies select over store") \
  BOOL_  (xform_instantiate_arrays,                     "xform.instantiate_arrays",                     false,          "Transforms P(a) into P(i, a[i] a)") \
  BOOL_  (xform_instantiate_arrays_enforce,             "xform.instantiate_arrays.enforce",             false,          "Transforms P(a) into P(i, a[i]), discards a from predicate") \
  UINT_  (xform_instantiate_arrays_nb_quantifier,       "xform.instantiate_arrays.nb_quantifier",       1,              "Gives the number of quantifiers per array") \
  SYMBOL_(xform_instantiate_arrays_slice_technique,     "xform.instantiate_arrays.slice_technique",     "no-slicing",   "<no-slicing>=> GetId(i) = i, <smash> => GetId(i) = true") \
  BOOL_  (xform_quantify_arrays,                        "xform.quantify_arrays",                        false,          "create quantified Horn clauses from clauses with arrays") \
  BOOL_  (xform_instantiate_quantifiers,                "xform.instantiate_quantifiers",                false,          "instantiate quantified Horn clauses using E-matching heuristic") \
  BOOL_  (xform_coalesce_rules,                         "xform.coalesce_rules",                         false,          "coalesce rules") \
  BOOL_  (xform_tail_simplifier_pve,                    "xform.tail_simplifier_pve",                    true,           "propagate_variable_equivalences") \
  BOOL_  (xform_subsumption_checker,                    "xform.subsumption_checker",                    true,           "Enable subsumption checker (no support for model conversion)") \
  BOOL_  (xform_coi,                                    "xform.coi",                                    true,           "use cone of influence simplification") \
  UINT_  (spacer_order_children,                        "spacer.order_children",                        0,              "SPACER: order of enqueuing children in non-linear rules : 0 (original), 1 (reverse), 2 (random)") \
  BOOL_  (spacer_use_lemma_as_cti,                      "spacer.use_lemma_as_cti",                      false,          "SPACER: use a lemma instead of a CTI in flexible_trace") \
  BOOL_  (spacer_reset_pob_queue,                       "spacer.reset_pob_queue",                       true,           "SPACER: reset pob obligation queue when entering a new level") \
  BOOL_  (spacer_use_array_eq_generalizer,              "spacer.use_array_eq_generalizer",              true,           "SPACER: attempt to generalize lemmas with array equalities") \
  BOOL_  (spacer_use_derivations,                       "spacer.use_derivations",                       true,           "SPACER: using derivation mechanism to cache intermediate results for non-linear rules") \
  BOOL_  (xform_array_blast,                            "xform.array_blast",                            false,          "try to eliminate local array terms using Ackermannization -- some array terms may remain") \
  BOOL_  (xform_array_blast_full,                       "xform.array_blast_full",                       false,          "eliminate all local array variables by QE") \
  BOOL_  (xform_elim_term_ite,                          "xform.elim_term_ite",                          false,          "Eliminate term-ite expressions") \
  UINT_  (xform_elim_term_ite_inflation,                "xform.elim_term_ite.inflation",                3,              "Maximum inflation for non-Boolean ite-terms blasting: 0 (none), k (multiplicative)") \
  BOOL_  (spacer_propagate,                             "spacer.propagate",                             true,           "Enable propagate/pushing phase") \
  UINT_  (spacer_max_level,                             "spacer.max_level",                             UINT_MAX,       "Maximum level to explore") \
  BOOL_  (spacer_elim_aux,                              "spacer.elim_aux",                              true,           "Eliminate auxiliary variables in reachability facts") \
  UINT_  (spacer_blast_term_ite_inflation,              "spacer.blast_term_ite_inflation",              3,              "Maximum inflation for non-Boolean ite-terms expansion: 0 (none), k (multiplicative)") \
  BOOL_  (spacer_reach_dnf,                             "spacer.reach_dnf",                             true,           "Restrict reachability facts to DNF") \
  UINT_  (bmc_linear_unrolling_depth,                   "bmc.linear_unrolling_depth",                   UINT_MAX,       "Maximal level to explore") \
  BOOL_  (spacer_iuc_split_farkas_literals,             "spacer.iuc.split_farkas_literals",             false,          "Split Farkas literals") \
  BOOL_  (spacer_native_mbp,                            "spacer.native_mbp",                            true,           "Use native mbp of Z3") \
  BOOL_  (spacer_eq_prop,                               "spacer.eq_prop",                               true,           "Enable equality and bound propagation in arithmetic") \
  BOOL_  (spacer_weak_abs,                              "spacer.weak_abs",                              true,           "Weak abstraction") \
  BOOL_  (spacer_restarts,                              "spacer.restarts",                              false,          "Enable resetting obligation queue") \
  UINT_  (spacer_restart_initial_threshold,             "spacer.restart_initial_threshold",             10,             "Initial threshold for restarts") \
  UINT_  (spacer_random_seed,                           "spacer.random_seed",                           0,              "Random seed to be used by SMT solver") \
  BOOL_  (spacer_mbqi,                                  "spacer.mbqi",                                  true,           "Enable mbqi") \
  BOOL_  (spacer_keep_proxy,                            "spacer.keep_proxy",                            true,           "keep proxy variables (internal parameter)") \
  BOOL_  (spacer_q3,                                    "spacer.q3",                                    true,           "Allow quantified lemmas in frames") \
  BOOL_  (spacer_q3_instantiate,                        "spacer.q3.instantiate",                        true,           "Instantiate quantified lemmas") \
  BOOL_  (spacer_q3_use_qgen,                           "spacer.q3.use_qgen",                           false,          "use quantified lemma generalizer") \
  BOOL_  (spacer_q3_qgen_normalize,                     "spacer.q3.qgen.normalize",                     true,           "normalize cube before quantified generalization") \
  UINT_  (spacer_iuc,                                   "spacer.iuc",                                   1,              "0 = use old implementation of unsat-core-generation, 1 = use new implementation of IUC generation, 2 = use new implementation of IUC + min-cut optimization") \
  UINT_  (spacer_iuc_arith,                             "spacer.iuc.arith",                             1,              "0 = use simple Farkas plugin, 1 = use simple Farkas plugin with constant from other partition (like old unsat-core-generation),2 = use Gaussian elimination optimization (broken), 3 = use additive IUC plugin") \
  BOOL_  (spacer_iuc_old_hyp_reducer,                   "spacer.iuc.old_hyp_reducer",                   false,          "use old hyp reducer instead of new implementation, for debugging only") \
  BOOL_  (spacer_validate_lemmas,                       "spacer.validate_lemmas",                       false,          "Validate each lemma after generalization") \
  BOOL_  (spacer_ground_pobs,                           "spacer.ground_pobs",                           true,           "Ground pobs by using values from a model") \
  BOOL_  (spacer_iuc_print_farkas_stats,                "spacer.iuc.print_farkas_stats",                false,          "prints for each proof how many Farkas lemmas it contains and how many of these participate in the cut (for debugging)") \
  BOOL_  (spacer_iuc_debug_proof,                       "spacer.iuc.debug_proof",                       false,          "prints proof used by unsat-core-learner for debugging purposes (debugging)") \
  BOOL_  (spacer_simplify_pob,                          "spacer.simplify_pob",                          false,          "simplify pobs by removing redundant constraints") \
  BOOL_  (spacer_p3_share_lemmas,                       "spacer.p3.share_lemmas",                       false,          "Share frame lemmas") \
  BOOL_  (spacer_p3_share_invariants,                   "spacer.p3.share_invariants",                   false,          "Share invariants lemmas") \
  UINT_  (spacer_min_level,                             "spacer.min_level",                             0,              "Minimal level to explore") \
  SYMBOL_(spacer_trace_file,                            "spacer.trace_file",                            "",             "Log file for progress events") \
  BOOL_  (spacer_ctp,                                   "spacer.ctp",                                   true,           "Enable counterexample-to-pushing") \
  BOOL_  (spacer_use_inc_clause,                        "spacer.use_inc_clause",                        true,           "Use incremental clause to represent trans") \
  BOOL_  (spacer_dump_benchmarks,                       "spacer.dump_benchmarks",                       false,          "Dump SMT queries as benchmarks") \
  DOUBLE_(spacer_dump_threshold,                        "spacer.dump_threshold",                        5.0,            "Threshold in seconds on dumping benchmarks") \
  BOOL_  (spacer_gpdr,                                  "spacer.gpdr",                                  false,          "Use GPDR solving strategy for non-linear CHC") \
  BOOL_  (spacer_gpdr_bfs,                              "spacer.gpdr.bfs",                              true,           "Use BFS exploration strategy for expanding model search") \
  BOOL_  (spacer_use_bg_invs,                           "spacer.use_bg_invs",                           false,          "Enable external background invariants") \
  BOOL_  (spacer_use_lim_num_gen,                       "spacer.use_lim_num_gen",                       false,          "Enable limit numbers generalizer to get smaller numbers") \
  SYMBOL_(spacer_logic,                                 "spacer.logic",                                 "",             "SMT-LIB logic to configure internal SMT solvers") \
  UINT_  (spacer_arith_solver,                          "spacer.arith.solver",                          2,              "arithmetic solver: 0 - no solver, 1 - bellman-ford based solver (diff. logic only), 2 - simplex based solver, 3 - floyd-warshall based solver (diff. logic only) and no theory combination 4 - utvpi, 5 - infinitary lra, 6 - lra solver") \
  BOOL_  (spacer_global,                                "spacer.global",                                false,          "Enable global guidance") \
  BOOL_  (spacer_gg_concretize,                         "spacer.gg.concretize",                         true,           "Enable global guidance concretize") \
  BOOL_  (spacer_gg_conjecture,                         "spacer.gg.conjecture",                         true,           "Enable global guidance conjecture") \
  BOOL_  (spacer_gg_subsume,                            "spacer.gg.subsume",                            true,           "Enable global guidance subsume") \
  BOOL_  (spacer_use_iuc,                               "spacer.use_iuc",                               true,           "Enable Interpolating Unsat Core(IUC) for lemma generalization") \
  BOOL_  (spacer_expand_bnd,                            "spacer.expand_bnd",                            false,          "Enable expand-bound lemma generalization")

Z3_DEFINE_MODULE_PARAMS(fp_params, "fp", FP_PARAMS_LIST, "fixedpoint parameters");

#undef FP_PARAMS_LIST
