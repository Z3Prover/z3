/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    combined_solver_params.hpp

Abstract:

    Parameters for the 'combined_solver' module.

--*/
#pragma once

#include "util/params.h"
#include "util/gparams.h"

#define COMBINED_SOLVER_PARAMS_LIST(UINT_, BOOL_, DOUBLE_, STRING_, SYMBOL_) \
  UINT_(solver2_timeout,  "solver2_timeout",  UINT_MAX,  "fallback to solver 1 after timeout even when in incremental model") \
  BOOL_(ignore_solver1,   "ignore_solver1",   false,     "if true, solver 2 is always used") \
  UINT_(solver2_unknown,  "solver2_unknown",  1,         "what should be done when solver 2 returns unknown: 0 - just return unknown, 1 - execute solver 1 if quantifier free problem, 2 - execute solver 1")

Z3_DEFINE_MODULE_PARAMS(combined_solver_params, "combined_solver", COMBINED_SOLVER_PARAMS_LIST, "combines two solvers: non-incremental (solver1) and incremental (solver2)");

#undef COMBINED_SOLVER_PARAMS_LIST
