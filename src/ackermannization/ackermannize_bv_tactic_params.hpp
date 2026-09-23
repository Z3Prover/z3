/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    ackermannize_bv_tactic_params.hpp

Abstract:

    Parameters for the 'rewriter' module.

--*/
#pragma once

#include "util/params.h"
#include "util/gparams.h"

#define ACKERMANNIZE_BV_TACTIC_PARAMS_LIST(UINT_, BOOL_, DOUBLE_, STRING_, SYMBOL_) \
  UINT_(div0_ackermann_limit,  "div0_ackermann_limit",  1000,  "a bound for number of congruence Ackermann lemmas for div0 modelling")

Z3_DEFINE_MODULE_PARAMS(ackermannize_bv_tactic_params, "rewriter", ACKERMANNIZE_BV_TACTIC_PARAMS_LIST, nullptr);

#undef ACKERMANNIZE_BV_TACTIC_PARAMS_LIST
