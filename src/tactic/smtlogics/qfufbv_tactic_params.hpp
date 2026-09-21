/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    qfufbv_tactic_params.hpp

Abstract:

    Parameters for the 'ackermannization' module.

--*/
#pragma once

#include "util/params.h"
#include "util/gparams.h"

#define QFUFBV_TACTIC_PARAMS_LIST(UINT_, BOOL_, DOUBLE_, STRING_, SYMBOL_) \
  BOOL_(sat_backend,      "sat_backend",      false,  "use SAT rather than SMT in qfufbv_ackr_tactic") \
  BOOL_(inc_sat_backend,  "inc_sat_backend",  false,  "use incremental SAT")

Z3_DEFINE_MODULE_PARAMS(qfufbv_tactic_params, "ackermannization", QFUFBV_TACTIC_PARAMS_LIST);

/*
   REG_MODULE_PARAMS('ackermannization', 'qfufbv_tactic_params::collect_param_descrs')
   REG_MODULE_DESCRIPTION('ackermannization', 'tactics based on solving UF-theories via ackermannization (see also ackr module)')
*/

#undef QFUFBV_TACTIC_PARAMS_LIST
