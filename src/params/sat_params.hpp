/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    sat_params.hpp

Abstract:

    Parameters for the 'sat' module.

--*/
#pragma once

#include "util/params.h"
#include "util/gparams.h"

#define SAT_PARAMS_LIST(UINT_, BOOL_, DOUBLE_, STRING_, SYMBOL_) \
  UINT_  (max_memory,                       "max_memory",                       UINT_MAX,       "maximum amount of memory in megabytes") \
  SYMBOL_(phase,                            "phase",                            "caching",      "phase selection strategy: always_false, always_true, basic_caching, random, caching, local_search") \
  BOOL_  (phase_sticky,                     "phase.sticky",                     true,           "use sticky phase caching") \
  UINT_  (search_unsat_conflicts,           "search.unsat.conflicts",           400,            "period for solving for unsat (in number of conflicts)") \
  UINT_  (search_sat_conflicts,             "search.sat.conflicts",             400,            "period for solving for sat (in number of conflicts)") \
  UINT_  (rephase_base,                     "rephase.base",                     1000,           "number of conflicts per rephase ") \
  UINT_  (reorder_base,                     "reorder.base",                     UINT_MAX,       "number of conflicts per random reorder ") \
  DOUBLE_(reorder_itau,                     "reorder.itau",                     4.0,            "inverse temperature for softmax") \
  UINT_  (reorder_activity_scale,           "reorder.activity_scale",           100,            "scaling factor for activity update") \
  BOOL_  (propagate_prefetch,               "propagate.prefetch",               true,           "prefetch watch lists for assigned literals") \
  SYMBOL_(restart,                          "restart",                          "ema",          "restart strategy: static, luby, ema or geometric") \
  UINT_  (restart_initial,                  "restart.initial",                  2,              "initial restart (number of conflicts)") \
  UINT_  (restart_max,                      "restart.max",                      UINT_MAX,       "maximal number of restarts.") \
  BOOL_  (restart_fast,                     "restart.fast",                     true,           "use fast restart approach only removing less active literals.") \
  DOUBLE_(restart_factor,                   "restart.factor",                   1.5,            "restart increment factor for geometric strategy") \
  DOUBLE_(restart_margin,                   "restart.margin",                   1.1,            "margin between fast and slow restart factors. For ema") \
  DOUBLE_(restart_emafastglue,              "restart.emafastglue",              0.03,           "ema alpha factor for fast moving average") \
  DOUBLE_(restart_emaslowglue,              "restart.emaslowglue",              1e-05,          "ema alpha factor for slow moving average") \
  UINT_  (variable_decay,                   "variable_decay",                   110,            "multiplier (divided by 100) for the VSIDS activity increment") \
  UINT_  (inprocess_max,                    "inprocess.max",                    UINT_MAX,       "maximal number of inprocessing passes") \
  SYMBOL_(inprocess_out,                    "inprocess.out",                    "",             "file to dump result of the first inprocessing step and exit") \
  SYMBOL_(branching_heuristic,              "branching.heuristic",              "vsids",        "branching heuristic vsids, chb") \
  BOOL_  (branching_anti_exploration,       "branching.anti_exploration",       false,          "apply anti-exploration heuristic for branch selection") \
  DOUBLE_(random_freq,                      "random_freq",                      0.01,           "frequency of random case splits") \
  UINT_  (random_seed,                      "random_seed",                      0,              "random seed") \
  UINT_  (burst_search,                     "burst_search",                     100,            "number of conflicts before first global simplification") \
  BOOL_  (enable_pre_simplify,              "enable_pre_simplify",              false,          "enable pre simplifications before the bounded search") \
  UINT_  (max_conflicts,                    "max_conflicts",                    UINT_MAX,       "maximum number of conflicts") \
  SYMBOL_(gc,                               "gc",                               "glue_psm",     "garbage collection strategy: psm, glue, glue_psm, dyn_psm") \
  UINT_  (gc_initial,                       "gc.initial",                       20000,          "learned clauses garbage collection frequency") \
  UINT_  (gc_increment,                     "gc.increment",                     500,            "increment to the garbage collection threshold") \
  UINT_  (gc_small_lbd,                     "gc.small_lbd",                     3,              "learned clauses with small LBD are never deleted (only used in dyn_psm)") \
  UINT_  (gc_k,                             "gc.k",                             7,              "learned clauses that are inactive for k gc rounds are permanently deleted (only used in dyn_psm)") \
  BOOL_  (gc_burst,                         "gc.burst",                         false,          "perform eager garbage collection during initialization") \
  BOOL_  (gc_defrag,                        "gc.defrag",                        true,           "defragment clauses when garbage collecting") \
  UINT_  (simplify_delay,                   "simplify.delay",                   0,              "set initial delay of simplification by a conflict count") \
  BOOL_  (force_cleanup,                    "force_cleanup",                    false,          "force cleanup to remove tautologies and simplify clauses") \
  BOOL_  (minimize_lemmas,                  "minimize_lemmas",                  true,           "minimize learned clauses") \
  BOOL_  (dyn_sub_res,                      "dyn_sub_res",                      true,           "dynamic subsumption resolution for minimizing learned clauses") \
  BOOL_  (core_minimize,                    "core.minimize",                    false,          "minimize computed core") \
  BOOL_  (core_minimize_partial,            "core.minimize_partial",            false,          "apply partial (cheap) core minimization") \
  UINT_  (backtrack_scopes,                 "backtrack.scopes",                 100,            "number of scopes to enable chronological backtracking") \
  UINT_  (backtrack_conflicts,              "backtrack.conflicts",              4000,           "number of conflicts before enabling chronological backtracking") \
  UINT_  (threads,                          "threads",                          1,              "number of parallel threads to use") \
  BOOL_  (dimacs_core,                      "dimacs.core",                      false,          "extract core from DIMACS benchmarks") \
  BOOL_  (drat_disable,                     "drat.disable",                     false,          "override anything that enables DRAT") \
  BOOL_  (smt,                              "smt",                              false,          "use the SAT solver based incremental SMT core") \
  BOOL_  (smt_proof_check,                  "smt.proof.check",                  false,          "check proofs on the fly during SMT search") \
  SYMBOL_(drat_file,                        "drat.file",                        "",             "file to dump DRAT proofs") \
  BOOL_  (drat_binary,                      "drat.binary",                      false,          "use Binary DRAT output format") \
  BOOL_  (drat_check_unsat,                 "drat.check_unsat",                 false,          "build up internal proof and check") \
  BOOL_  (drat_check_sat,                   "drat.check_sat",                   false,          "build up internal trace, check satisfying model") \
  BOOL_  (drat_activity,                    "drat.activity",                    false,          "dump variable activities") \
  BOOL_  (cardinality_solver,               "cardinality.solver",               true,           "use cardinality solver") \
  SYMBOL_(pb_solver,                        "pb.solver",                        "solver",       "method for handling Pseudo-Boolean constraints: circuit (arithmetical circuit), sorting (sorting circuit), totalizer (use totalizer encoding), binary_merge, segmented, solver (use native solver)") \
  UINT_  (pb_min_arity,                     "pb.min_arity",                     9,              "minimal arity to compile pb/cardinality constraints to CNF") \
  SYMBOL_(cardinality_encoding,             "cardinality.encoding",             "grouped",      "encoding used for at-most-k constraints: grouped, bimander, ordered, unate, circuit") \
  SYMBOL_(pb_resolve,                       "pb.resolve",                       "cardinality",  "resolution strategy for boolean algebra solver: cardinality, rounding") \
  SYMBOL_(pb_lemma_format,                  "pb.lemma_format",                  "cardinality",  "generate either cardinality or pb lemmas") \
  BOOL_  (euf,                              "euf",                              false,          "enable euf solver (this feature is preliminary and not ready for general consumption)") \
  BOOL_  (ddfw_search,                      "ddfw_search",                      false,          "use ddfw local search instead of CDCL") \
  UINT_  (ddfw_init_clause_weight,          "ddfw.init_clause_weight",          8,              "initial clause weight for DDFW local search") \
  UINT_  (ddfw_use_reward_pct,              "ddfw.use_reward_pct",              15,             "percentage to pick highest reward variable when it has reward 0") \
  UINT_  (ddfw_restart_base,                "ddfw.restart_base",                100000,         "number of flips used a starting point for hesitant restart backoff") \
  UINT_  (ddfw_reinit_base,                 "ddfw.reinit_base",                 10000,          "increment basis for geometric backoff scheme of re-initialization of weights") \
  UINT_  (ddfw_threads,                     "ddfw.threads",                     0,              "number of ddfw threads to run in parallel with sat solver") \
  BOOL_  (prob_search,                      "prob_search",                      false,          "use probsat local search instead of CDCL") \
  BOOL_  (local_search,                     "local_search",                     false,          "use local search instead of CDCL") \
  UINT_  (local_search_threads,             "local_search_threads",             0,              "number of local search threads to find satisfiable solution") \
  SYMBOL_(local_search_mode,                "local_search_mode",                "wsat",         "local search algorithm, either default wsat or qsat") \
  BOOL_  (local_search_dbg_flips,           "local_search_dbg_flips",           false,          "write debug information for number of flips") \
  BOOL_  (anf,                              "anf",                              false,          "enable ANF based simplification in-processing") \
  UINT_  (anf_delay,                        "anf.delay",                        2,              "delay ANF simplification by in-processing round") \
  BOOL_  (anf_exlin,                        "anf.exlin",                        false,          "enable extended linear simplification") \
  SYMBOL_(lookahead_cube_cutoff,            "lookahead.cube.cutoff",            "depth",        "cutoff type used to create lookahead cubes: depth, freevars, psat, adaptive_freevars, adaptive_psat") \
  DOUBLE_(lookahead_cube_fraction,          "lookahead.cube.fraction",          0.4,            "adaptive fraction to create lookahead cubes. Used when lookahead.cube.cutoff is adaptive_freevars or adaptive_psat") \
  UINT_  (lookahead_cube_depth,             "lookahead.cube.depth",             1,              "cut-off depth to create cubes. Used when lookahead.cube.cutoff is depth.") \
  DOUBLE_(lookahead_cube_freevars,          "lookahead.cube.freevars",          0.8,            "cube free variable fraction. Used when lookahead.cube.cutoff is freevars") \
  DOUBLE_(lookahead_cube_psat_var_exp,      "lookahead.cube.psat.var_exp",      1,              "free variable exponent for PSAT cutoff") \
  DOUBLE_(lookahead_cube_psat_clause_base,  "lookahead.cube.psat.clause_base",  2,              "clause base for PSAT cutoff") \
  DOUBLE_(lookahead_cube_psat_trigger,      "lookahead.cube.psat.trigger",      5,              "trigger value to create lookahead cubes for PSAT cutoff. Used when lookahead.cube.cutoff is psat") \
  BOOL_  (lookahead_preselect,              "lookahead.preselect",              false,          "use pre-selection of subset of variables for branching") \
  BOOL_  (lookahead_simplify,               "lookahead_simplify",               false,          "use lookahead solver during simplification") \
  BOOL_  (lookahead_scores,                 "lookahead_scores",                 false,          "extract lookahead scores. A utility that can only be used from the DIMACS front-end") \
  BOOL_  (lookahead_double,                 "lookahead.double",                 true,           "enable double lookahead") \
  BOOL_  (lookahead_use_learned,            "lookahead.use_learned",            false,          "use learned clauses when selecting lookahead literal") \
  BOOL_  (lookahead_simplify_bca,           "lookahead_simplify.bca",           true,           "add learned binary clauses as part of lookahead simplification") \
  BOOL_  (lookahead_global_autarky,         "lookahead.global_autarky",         false,          "prefer to branch on variables that occur in clauses that are reduced") \
  DOUBLE_(lookahead_delta_fraction,         "lookahead.delta_fraction",         1.0,            "number between 0 and 1, the smaller the more literals are selected for double lookahead") \
  SYMBOL_(lookahead_reward,                 "lookahead.reward",                 "march_cu",     "select lookahead heuristic: ternary, heule_schur (Heule Schur), heuleu (Heule Unit), unit, or march_cu")

Z3_DEFINE_MODULE_PARAMS(sat_params, "sat", SAT_PARAMS_LIST, "propositional SAT solver");

#undef SAT_PARAMS_LIST
