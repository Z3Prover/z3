/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    poly_rewriter_params.hpp

Abstract:

    Parameters for the 'rewriter' module.

--*/
#pragma once

#include "util/params.h"
#include "util/gparams.h"

#define POLY_REWRITER_PARAMS_LIST(UINT_, BOOL_, DOUBLE_, STRING_, SYMBOL_) \
  BOOL_(som,         "som",         false,  "put polynomials in sum-of-monomials form") \
  UINT_(som_blowup,  "som_blowup",  10,     "maximum increase of monomials generated when putting a polynomial in sum-of-monomials normal form") \
  BOOL_(hoist_mul,   "hoist_mul",   false,  "hoist multiplication over summation to minimize number of multiplications") \
  BOOL_(hoist_ite,   "hoist_ite",   false,  "hoist shared summands under ite expressions") \
  BOOL_(flat,        "flat",        true,   "create nary applications for and,or,+,*,bvadd,bvmul,bvand,bvor,bvxor")

Z3_DEFINE_MODULE_PARAMS(poly_rewriter_params, "rewriter", POLY_REWRITER_PARAMS_LIST, nullptr);

#undef POLY_REWRITER_PARAMS_LIST
