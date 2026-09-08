/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    model_evaluator_params.hpp

Abstract:

    Parameters for the 'model_evaluator' module.

--*/
#pragma once

#include "util/params.h"
#include "util/gparams.h"

#define MODEL_EVALUATOR_PARAMS_LIST(UINT_, BOOL_, DOUBLE_, STRING_, SYMBOL_) \
  UINT_(max_memory,        "max_memory",        UINT_MAX,  "maximum amount of memory in megabytes") \
  UINT_(max_steps,         "max_steps",         UINT_MAX,  "maximum number of steps") \
  BOOL_(completion,        "completion",        false,     "assigns an interptetation to symbols that do not have one in the current model, when evaluating expressions in the current model") \
  BOOL_(array_equalities,  "array_equalities",  true,      "evaluate array equalities") \
  BOOL_(array_as_stores,   "array_as_stores",   true,      "return array as a set of stores")

Z3_DEFINE_MODULE_PARAMS(model_evaluator_params, "model_evaluator", MODEL_EVALUATOR_PARAMS_LIST);

/*
   REG_MODULE_PARAMS('model_evaluator', 'model_evaluator_params::collect_param_descrs')
*/

#undef MODEL_EVALUATOR_PARAMS_LIST
