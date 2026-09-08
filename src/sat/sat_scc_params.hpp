/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    sat_scc_params.hpp

Abstract:

    Parameters for the 'sat' module.

--*/
#pragma once

#include "util/params.h"
#include "util/gparams.h"

#define SAT_SCC_PARAMS_LIST(UINT_, BOOL_, DOUBLE_, STRING_, SYMBOL_) \
  BOOL_(scc,     "scc",     true,  "eliminate Boolean variables by computing strongly connected components") \
  BOOL_(scc_tr,  "scc.tr",  true,  "apply transitive reduction, eliminate redundant binary clauses")

Z3_DEFINE_MODULE_PARAMS(sat_scc_params, "sat", SAT_SCC_PARAMS_LIST, nullptr);

#undef SAT_SCC_PARAMS_LIST
