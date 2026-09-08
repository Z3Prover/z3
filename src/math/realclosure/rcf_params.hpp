/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    rcf_params.hpp

Abstract:

    Parameters for the 'rcf' module.

--*/
#pragma once

#include "util/params.h"
#include "util/gparams.h"

#define RCF_PARAMS_LIST(UINT_, BOOL_, DOUBLE_, STRING_, SYMBOL_) \
  BOOL_(use_prem,                      "use_prem",                      true,  "use pseudo-remainder instead of remainder when computing GCDs and Sturm-Tarski sequences") \
  BOOL_(clean_denominators,            "clean_denominators",            true,  "clean denominators before root isolation") \
  UINT_(initial_precision,             "initial_precision",             24,    "a value k that is the initial interval size (as 1/2^k) when creating transcendentals and approximated division") \
  UINT_(inf_precision,                 "inf_precision",                 24,    "a value k that is the initial interval size (i.e., (0, 1/2^l)) used as an approximation for infinitesimal values") \
  UINT_(max_precision,                 "max_precision",                 128,   "during sign determination we switch from interval arithmetic to complete methods when the interval size is less than 1/2^k, where k is the max_precision") \
  BOOL_(lazy_algebraic_normalization,  "lazy_algebraic_normalization",  true,  "during sturm-seq and square-free polynomial computations, only normalize algebraic polynomial expressions when the defining polynomial is monic")

Z3_DEFINE_MODULE_PARAMS(rcf_params, "rcf", RCF_PARAMS_LIST);

/*
   REG_MODULE_PARAMS('rcf', 'rcf_params::collect_param_descrs')
   REG_MODULE_DESCRIPTION('rcf', 'real closed fields')
*/

#undef RCF_PARAMS_LIST
