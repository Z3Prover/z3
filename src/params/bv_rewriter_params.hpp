/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    bv_rewriter_params.hpp

Abstract:

    Parameters for the 'rewriter' module.

--*/
#pragma once

#include "util/params.h"
#include "util/gparams.h"

#define BV_REWRITER_PARAMS_LIST(UINT_, BOOL_, DOUBLE_, STRING_, SYMBOL_) \
  BOOL_(split_concat_eq,  "split_concat_eq",  false,  "split equalities of the form (= (concat t1 t2) t3)") \
  BOOL_(bit2bool,         "bit2bool",         true,   "try to convert bit-vector terms of size 1 into Boolean terms") \
  BOOL_(blast_eq_value,   "blast_eq_value",   false,  "blast (some) Bit-vector equalities into bits") \
  BOOL_(elim_sign_ext,    "elim_sign_ext",    true,   "expand sign-ext operator using concat and extract") \
  BOOL_(hi_div0,          "hi_div0",          true,   "use the 'hardware interpretation' for division by zero (for bit-vector terms)") \
  BOOL_(mul2concat,       "mul2concat",       false,  "replace multiplication by a power of two into a concatenation") \
  BOOL_(bv_sort_ac,       "bv_sort_ac",       true,   "sort the arguments of all AC operators") \
  BOOL_(bv_extract_prop,  "bv_extract_prop",  false,  "attempt to partially propagate extraction inwards") \
  BOOL_(bv_not_simpl,     "bv_not_simpl",     false,  "apply simplifications for bvnot") \
  BOOL_(bv_ite2id,        "bv_ite2id",        false,  "rewrite ite that can be simplified to identity") \
  BOOL_(bv_le_extra,      "bv_le_extra",      false,  "additional bu_(u/s)le simplifications") \
  BOOL_(bv_le2extract,    "bv_le2extract",    true,   "disassemble bvule to extract")

Z3_DEFINE_MODULE_PARAMS(bv_rewriter_params, "rewriter", BV_REWRITER_PARAMS_LIST, nullptr);

#undef BV_REWRITER_PARAMS_LIST
