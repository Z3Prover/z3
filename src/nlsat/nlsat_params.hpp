/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    nlsat_params.hpp

Abstract:

    Parameters for the 'nlsat' module.

--*/
#pragma once

#include "util/params.h"
#include "util/gparams.h"

#define NLSAT_PARAMS_LIST(UINT_, BOOL_, DOUBLE_, STRING_, SYMBOL_) \
  UINT_  (max_memory,                      "max_memory",                      UINT_MAX,  "maximum amount of memory in megabytes") \
  BOOL_  (simple_check,                    "simple_check",                    false,     "precheck polynomials using variables sign") \
  UINT_  (variable_ordering_strategy,      "variable_ordering_strategy",      0,         "Variable Ordering Strategy, 0 for none, 1 for BROWN, 2 for TRIANGULAR, 3 for ONLYPOLY") \
  UINT_  (lazy,                            "lazy",                            0,         "how lazy the solver is.") \
  BOOL_  (reorder,                         "reorder",                         true,      "reorder variables.") \
  BOOL_  (log_lemmas,                      "log_lemmas",                      false,     "display lemmas as self-contained SMT formulas") \
  BOOL_  (log_lemma_smtrat,                "log_lemma_smtrat",                false,     "log lemmas to be readable by smtrat") \
  BOOL_  (dump_mathematica,                "dump_mathematica",                false,     "display lemmas as matematica") \
  BOOL_  (check_lemmas,                    "check_lemmas",                    false,     "check lemmas on the fly using an independent nlsat solver") \
  BOOL_  (simplify_conflicts,              "simplify_conflicts",              true,      "simplify conflicts using equalities before resolving them in nlsat solver.") \
  BOOL_  (minimize_conflicts,              "minimize_conflicts",              false,     "minimize conflicts") \
  BOOL_  (randomize,                       "randomize",                       true,      "randomize selection of a witness in nlsat.") \
  UINT_  (max_conflicts,                   "max_conflicts",                   UINT_MAX,  "maximum number of conflicts.") \
  BOOL_  (shuffle_vars,                    "shuffle_vars",                    false,     "use a random variable order.") \
  BOOL_  (inline_vars,                     "inline_vars",                     false,     "inline variables that can be isolated from equations (not supported in incremental mode)") \
  UINT_  (seed,                            "seed",                            0,         "random seed.") \
  BOOL_  (factor,                          "factor",                          true,      "factor polynomials produced during conflict resolution.") \
  BOOL_  (add_all_coeffs,                  "add_all_coeffs",                  false,     "add all polynomial coefficients during projection.") \
  BOOL_  (zero_disc,                       "zero_disc",                       false,     "add_zero_assumption to the vanishing discriminant.") \
  STRING_(known_sat_assignment_file_name,  "known_sat_assignment_file_name",  "",        "the file name of a known solution: used for debugging only") \
  BOOL_  (lws,                             "lws",                             true,      "apply levelwise.") \
  UINT_  (lws_spt_threshold,               "lws_spt_threshold",               4,         "minimum both-side polynomial count to apply spanning tree optimization; < 2 disables spanning tree") \
  BOOL_  (lws_witness_subs_lc,             "lws_witness_subs_lc",             true,      "try substitute the non-nullified witness by the lc") \
  BOOL_  (lws_witness_subs_disc,           "lws_witness_subs_disc",           true,      "try substitute the non-nullified witness by the discriminant") \
  BOOL_  (canonicalize,                    "canonicalize",                    true,      "canonicalize polynomials.")

Z3_DEFINE_MODULE_PARAMS(nlsat_params, "nlsat", NLSAT_PARAMS_LIST, "nonlinear solver");

#undef NLSAT_PARAMS_LIST
