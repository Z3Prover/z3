/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    rewriter_params.hpp

Abstract:

    Parameters for the 'rewriter' module.

--*/
#pragma once

#include "util/params.h"
#include "util/gparams.h"

#define REWRITER_PARAMS_LIST(UINT_, BOOL_, DOUBLE_, STRING_, SYMBOL_) \
  UINT_(max_memory,                       "max_memory",                       UINT_MAX,  "maximum amount of memory in megabytes") \
  UINT_(max_steps,                        "max_steps",                        UINT_MAX,  "maximum number of steps") \
  BOOL_(push_ite_arith,                   "push_ite_arith",                   false,     "push if-then-else over arithmetic terms.") \
  BOOL_(push_ite_bv,                      "push_ite_bv",                      false,     "push if-then-else over bit-vector terms.") \
  BOOL_(pull_cheap_ite,                   "pull_cheap_ite",                   false,     "pull if-then-else terms when cheap.") \
  UINT_(bv_ineq_consistency_test_max,     "bv_ineq_consistency_test_max",     0,         "max size of conjunctions on which to perform consistency test based on inequalities on bitvectors.") \
  BOOL_(unfold_recursive_functions,       "unfold_recursive_functions",       false,     "apply simplification recursively on recursive functions.") \
  BOOL_(cache_all,                        "cache_all",                        false,     "cache all intermediate results.") \
  BOOL_(enable_der,                       "enable_der",                       true,      "enable destructive equality resolution to quantifiers.") \
  BOOL_(rewrite_patterns,                 "rewrite_patterns",                 false,     "rewrite patterns.") \
  BOOL_(ignore_patterns_on_ground_qbody,  "ignore_patterns_on_ground_qbody",  true,      "ignores patterns on quantifiers that don't mention their bound variables.")

Z3_DEFINE_MODULE_PARAMS(rewriter_params, "rewriter", REWRITER_PARAMS_LIST, "new formula simplification module used in the tactic framework, and new solvers");

#undef REWRITER_PARAMS_LIST
