/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    sat_asymm_branch_params.hpp

Abstract:

    Parameters for the 'sat' module.

--*/
#pragma once

#include "util/params.h"
#include "util/gparams.h"

#define SAT_ASYMM_BRANCH_PARAMS_LIST(UINT_, BOOL_, DOUBLE_, STRING_, SYMBOL_) \
  BOOL_(asymm_branch,          "asymm_branch",          true,       "asymmetric branching") \
  UINT_(asymm_branch_rounds,   "asymm_branch.rounds",   2,          "maximal number of rounds to run asymmetric branch simplifications if progress is made") \
  UINT_(asymm_branch_delay,    "asymm_branch.delay",    1,          "number of simplification rounds to wait until invoking asymmetric branch simplification") \
  BOOL_(asymm_branch_sampled,  "asymm_branch.sampled",  true,       "use sampling based asymmetric branching based on binary implication graph") \
  UINT_(asymm_branch_limit,    "asymm_branch.limit",    100000000,  "approx. maximum number of literals visited during asymmetric branching") \
  BOOL_(asymm_branch_all,      "asymm_branch.all",      false,      "asymmetric branching on all literals per clause")

Z3_DEFINE_MODULE_PARAMS(sat_asymm_branch_params, "sat", SAT_ASYMM_BRANCH_PARAMS_LIST, nullptr);

#undef SAT_ASYMM_BRANCH_PARAMS_LIST
