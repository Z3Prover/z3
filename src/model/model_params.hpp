/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    model_params.hpp

Abstract:

    Parameters for the 'model' module.

--*/
#pragma once

#include "util/params.h"
#include "util/gparams.h"

#define MODEL_PARAMS_LIST(UINT_, BOOL_, DOUBLE_, STRING_, SYMBOL_) \
  BOOL_(partial,         "partial",         false,  "enable/disable partial function interpretations") \
  BOOL_(v1,              "v1",              false,  "use Z3 version 1.x pretty printer") \
  BOOL_(v2,              "v2",              false,  "use Z3 version 2.x (x <= 16) pretty printer") \
  BOOL_(compact,         "compact",         true,   "try to compact function graph (i.e., function interpretations that are lookup tables)") \
  BOOL_(inline_def,      "inline_def",      false,  "inline local function definitions ignoring possible expansion") \
  BOOL_(user_functions,  "user_functions",  true,   "include user defined functions in model") \
  BOOL_(completion,      "completion",      false,  "enable/disable model completion")

Z3_DEFINE_MODULE_PARAMS(model_params, "model", MODEL_PARAMS_LIST, nullptr);

#undef MODEL_PARAMS_LIST
