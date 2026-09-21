/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    opt_params.hpp

Abstract:

    Parameters for the 'opt' module.

--*/
#pragma once

#include "util/params.h"
#include "util/gparams.h"

#define OPT_PARAMS_LIST(UINT_, BOOL_, DOUBLE_, STRING_, SYMBOL_) \
  SYMBOL_(optsmt_engine,                   "optsmt_engine",                   "basic",   "select optimization engine: 'basic', 'symba'") \
  UINT_  (optsmt_bisect_rounds,            "optsmt_bisect_rounds",            64,        "maximal number of solver calls spent bisecting the interval between the best model value and the refuted arithmetic bound of a real-valued objective (e.g. under nonlinear constraints); when exhausted the objective is reported as unknown with that interval") \
  BOOL_  (optsmt_nlsat,                    "optsmt_nlsat",                    true,      "optimize real objectives under nonlinear constraints exactly over nlsat cells (algebraic optima print as root-obj; unboundedness proven by native nlsat projection under an escalating rlimit budget)") \
  UINT_  (optsmt_nlsat_supremum_rlimit,    "optsmt_nlsat_supremum_rlimit",    100000,    "resource limit for certifying finite open suprema with native nlsat projection (0 disables the extra check)") \
  BOOL_  (pareto_nlsat,                    "pareto_nlsat",                    true,      "enumerate Pareto fronts of pure NRA problems over an nlsat-backed solver, comparing objectives against exact algebraic model values instead of rounded isolating-interval endpoints") \
  BOOL_  (pareto_nlsat_reuse,              "pareto_nlsat_reuse",              true,      "reuse nlsat clauses across Pareto checks on polynomial real problems; false keeps the exact solver that starts each check from scratch") \
  UINT_  (pareto_nlsat_max_lemmas,         "pareto_nlsat_max_lemmas",         128,       "maximum number of independent learned clauses retained between Pareto climbs; shorter clauses are preferred") \
  SYMBOL_(maxsat_engine,                   "maxsat_engine",                   "maxres",  "select engine for maxsat: 'core_maxsat', 'wmax', 'maxres', 'maxresw', 'pd-maxres', 'maxres-bin', 'rc2'") \
  SYMBOL_(priority,                        "priority",                        "lex",     "select how to prioritize objectives: 'lex' (lexicographic), 'pareto', 'box'") \
  BOOL_  (dump_benchmarks,                 "dump_benchmarks",                 false,     "dump benchmarks for profiling") \
  BOOL_  (dump_models,                     "dump_models",                     false,     "display intermediary models to stdout") \
  SYMBOL_(solution_prefix,                 "solution_prefix",                 "",        "path prefix to dump intermediary, but non-optimal, solutions") \
  UINT_  (timeout,                         "timeout",                         UINT_MAX,  "timeout (in milliseconds) (UINT_MAX and 0 mean no timeout)") \
  UINT_  (rlimit,                          "rlimit",                          0,         "resource limit (0 means no limit)") \
  BOOL_  (enable_sls,                      "enable_sls",                      false,     "enable SLS tuning during weighted maxsat") \
  BOOL_  (enable_lns,                      "enable_lns",                      false,     "enable LNS during weighted maxsat") \
  UINT_  (lns_conflicts,                   "lns_conflicts",                   1000,      "initial conflict count for LNS search") \
  BOOL_  (enable_core_rotate,              "enable_core_rotate",              false,     "enable core rotation to both sample cores and correction sets") \
  BOOL_  (enable_sat,                      "enable_sat",                      true,      "enable the new SAT core for propositional constraints") \
  BOOL_  (elim_01,                         "elim_01",                         true,      "eliminate 01 variables") \
  BOOL_  (incremental,                     "incremental",                     false,     "set incremental mode. It disables pre-processing and enables adding constraints in model event handler") \
  BOOL_  (pp_neat,                         "pp.neat",                         true,      "use neat (as opposed to less readable, but faster) pretty printer when displaying context") \
  BOOL_  (pb_compile_equality,             "pb.compile_equality",             false,     "compile arithmetical equalities into pseudo-Boolean equality (instead of two inequalites)") \
  BOOL_  (pp_wcnf,                         "pp.wcnf",                         false,     "print maxsat benchmark into wcnf format") \
  BOOL_  (maxlex_enable,                   "maxlex.enable",                   true,      "enable maxlex heuristic for lexicographic MaxSAT problems") \
  BOOL_  (rc2_totalizer,                   "rc2.totalizer",                   true,      "use totalizer for rc2 encoding") \
  BOOL_  (maxres_hill_climb,               "maxres.hill_climb",               true,      "give preference for large weight cores") \
  BOOL_  (maxres_add_upper_bound_block,    "maxres.add_upper_bound_block",    false,     "restrict upper bound with constraint") \
  UINT_  (maxres_max_num_cores,            "maxres.max_num_cores",            200,       "maximal number of cores per round") \
  UINT_  (maxres_max_core_size,            "maxres.max_core_size",            3,         "break batch of generated cores if size reaches this number") \
  BOOL_  (maxres_maximize_assignment,      "maxres.maximize_assignment",      false,     "find an MSS/MCS to improve current assignment") \
  UINT_  (maxres_max_correction_set_size,  "maxres.max_correction_set_size",  3,         "allow generating correction set constraints up to maximal size") \
  BOOL_  (maxres_wmax,                     "maxres.wmax",                     false,     "use weighted theory solver to constrain upper bounds") \
  BOOL_  (maxres_pivot_on_correction_set,  "maxres.pivot_on_correction_set",  true,      "reduce soft constraints if the current correction set is smaller than current core")

Z3_DEFINE_MODULE_PARAMS(opt_params, "opt", OPT_PARAMS_LIST);

/*
   REG_MODULE_PARAMS('opt', 'opt_params::collect_param_descrs')
   REG_MODULE_DESCRIPTION('opt', 'optimization parameters')
*/

#undef OPT_PARAMS_LIST
