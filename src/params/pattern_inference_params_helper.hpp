/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    pattern_inference_params_helper.hpp

Abstract:

    Parameters for the 'pi' module.

--*/
#pragma once

#include "util/params.h"
#include "util/gparams.h"

#define PATTERN_INFERENCE_PARAMS_HELPER_LIST(UINT_, BOOL_, DOUBLE_, STRING_, SYMBOL_) \
  UINT_(max_multi_patterns,       "max_multi_patterns",       0,      "when patterns are not provided, the prover uses a heuristic to infer them, this option sets the threshold on the number of extra multi-patterns that can be created; by default, the prover creates at most one multi-pattern when there is no unary pattern") \
  BOOL_(block_loop_patterns,      "block_loop_patterns",      true,   "block looping patterns during pattern inference") \
  BOOL_(decompose_patterns,       "decompose_patterns",       true,   "allow decomposition of patterns into multipatterns") \
  UINT_(arith,                    "arith",                    1,      "0 - do not infer patterns with arithmetic terms, 1 - use patterns with arithmetic terms if there is no other pattern, 2 - always use patterns with arithmetic terms") \
  BOOL_(use_database,             "use_database",             false,  "use pattern database") \
  BOOL_(enabled,                  "enabled",                  true,   "enable a heuristic to infer patterns, when they are not provided") \
  UINT_(arith_weight,             "arith_weight",             5,      "default weight for quantifiers where the only available pattern has nested arithmetic terms") \
  UINT_(non_nested_arith_weight,  "non_nested_arith_weight",  10,     "default weight for quantifiers where the only available pattern has non nested arithmetic terms") \
  BOOL_(pull_quantifiers,         "pull_quantifiers",         true,   "pull nested quantifiers, if no pattern was found") \
  BOOL_(avoid_skolems,            "avoid_skolems",            true,   "avoid skolem functions when computing patterns") \
  BOOL_(warnings,                 "warnings",                 false,  "enable/disable warning messages in the pattern inference module")

Z3_DEFINE_MODULE_PARAMS(pattern_inference_params_helper, "pi", PATTERN_INFERENCE_PARAMS_HELPER_LIST);

/*
   REG_MODULE_PARAMS('pi', 'pattern_inference_params_helper::collect_param_descrs')
   REG_MODULE_DESCRIPTION('pi', 'pattern inference (heuristics) for universal formulas (without annotation)')
*/

#undef PATTERN_INFERENCE_PARAMS_HELPER_LIST
