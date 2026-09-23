/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    array_rewriter_params.hpp

Abstract:

    Parameters for the 'rewriter' module.

--*/
#pragma once

#include "util/params.h"
#include "util/gparams.h"

#define ARRAY_REWRITER_PARAMS_LIST(UINT_, BOOL_, DOUBLE_, STRING_, SYMBOL_) \
  BOOL_(expand_select_store,   "expand_select_store",   false,  "conservatively replace a (select (store ...) ...) term by an if-then-else term") \
  BOOL_(blast_select_store,    "blast_select_store",    false,  "eagerly replace all (select (store ..) ..) term by an if-then-else term") \
  BOOL_(expand_nested_stores,  "expand_nested_stores",  false,  "replace nested stores by a lambda expression") \
  BOOL_(expand_select_ite,     "expand_select_ite",     false,  "expand select over ite expressions") \
  BOOL_(expand_store_eq,       "expand_store_eq",       false,  "reduce (store ...) = (store ...) with a common base into selects") \
  BOOL_(sort_store,            "sort_store",            false,  "sort nested stores when the indices are known to be different")

Z3_DEFINE_MODULE_PARAMS(array_rewriter_params, "rewriter", ARRAY_REWRITER_PARAMS_LIST, nullptr);

#undef ARRAY_REWRITER_PARAMS_LIST
