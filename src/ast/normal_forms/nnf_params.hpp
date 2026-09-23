/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    nnf_params.hpp

Abstract:

    Parameters for the 'nnf' module.

--*/
#pragma once

#include "util/params.h"
#include "util/gparams.h"

#define NNF_PARAMS_LIST(UINT_, BOOL_, DOUBLE_, STRING_, SYMBOL_) \
  UINT_  (max_memory,     "max_memory",     UINT_MAX,  "maximum amount of memory in megabytes") \
  BOOL_  (sk_hack,        "sk_hack",        false,     "hack for VCC") \
  SYMBOL_(mode,           "mode",           "skolem",  "NNF translation mode: skolem (skolem normal form), quantifiers (skolem normal form + quantifiers in NNF), full") \
  BOOL_  (ignore_labels,  "ignore_labels",  false,     "remove/ignore labels in the input formula, this option is ignored if proofs are enabled")

Z3_DEFINE_MODULE_PARAMS(nnf_params, "nnf", NNF_PARAMS_LIST, "negation normal form");

#undef NNF_PARAMS_LIST
