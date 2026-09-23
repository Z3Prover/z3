/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    ackermannization_params.hpp

Abstract:

    Parameters for the 'ackermannization' module.

--*/
#pragma once

#include "util/params.h"
#include "util/gparams.h"

#define ACKERMANNIZATION_PARAMS_LIST(UINT_, BOOL_, DOUBLE_, STRING_, SYMBOL_) \
  BOOL_(eager,  "eager",  true,  "eagerly instantiate all congruence rules")

Z3_DEFINE_MODULE_PARAMS(ackermannization_params, "ackermannization", ACKERMANNIZATION_PARAMS_LIST, "solving UF via ackermannization");

#undef ACKERMANNIZATION_PARAMS_LIST
