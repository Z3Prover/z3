/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    parser_params.hpp

Abstract:

    Parameters for the 'parser' module.

--*/
#pragma once

#include "util/params.h"
#include "util/gparams.h"

#define PARSER_PARAMS_LIST(UINT_, BOOL_, DOUBLE_, STRING_, SYMBOL_) \
  BOOL_(ignore_user_patterns,     "ignore_user_patterns",     false,  "ignore patterns provided by the user") \
  BOOL_(ignore_bad_patterns,      "ignore_bad_patterns",      true,   "ignore malformed patterns") \
  BOOL_(error_for_visual_studio,  "error_for_visual_studio",  false,  "display error messages in Visual Studio format")

Z3_DEFINE_MODULE_PARAMS(parser_params, "parser", PARSER_PARAMS_LIST, nullptr);

#undef PARSER_PARAMS_LIST
