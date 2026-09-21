/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    arith_rewriter_params.hpp

Abstract:

    Parameters for the 'rewriter' module.

--*/
#pragma once

#include "util/params.h"
#include "util/gparams.h"

#define ARITH_REWRITER_PARAMS_LIST(UINT_, BOOL_, DOUBLE_, STRING_, SYMBOL_) \
  BOOL_(algebraic_number_evaluator,  "algebraic_number_evaluator",  true,   "simplify/evaluate expressions containing (algebraic) irrational numbers.") \
  BOOL_(mul_to_power,                "mul_to_power",                false,  "collpase (* t ... t) into (^ t k), it is ignored if expand_power is true.") \
  BOOL_(expand_power,                "expand_power",                false,  "expand (^ t k) into (* t ... t) if  1 < k <= max_degree.") \
  BOOL_(expand_tan,                  "expand_tan",                  false,  "replace (tan x) with (/ (sin x) (cos x)).") \
  UINT_(max_degree,                  "max_degree",                  64,     "max degree of algebraic numbers (and power operators) processed by simplifier.") \
  BOOL_(sort_sums,                   "sort_sums",                   false,  "sort the arguments of + application.") \
  BOOL_(gcd_rounding,                "gcd_rounding",                false,  "use gcd rounding on integer arithmetic atoms.") \
  BOOL_(arith_lhs,                   "arith_lhs",                   false,  "all monomials are moved to the left-hand-side, and the right-hand-side is just a constant.") \
  BOOL_(arith_ineq_lhs,              "arith_ineq_lhs",              false,  "rewrite inequalities so that right-hand-side is a constant.") \
  BOOL_(elim_to_real,                "elim_to_real",                false,  "eliminate to_real from arithmetic predicates that contain only integers.") \
  BOOL_(push_to_real,                "push_to_real",                true,   "distribute to_real over * and +.") \
  BOOL_(eq2ineq,                     "eq2ineq",                     false,  "expand equalities into two inequalities") \
  BOOL_(elim_rem,                    "elim_rem",                    false,  "replace (rem x y) with (ite (>= y 0) (mod x y) (- (mod x y))).")

Z3_DEFINE_MODULE_PARAMS(arith_rewriter_params, "rewriter", ARITH_REWRITER_PARAMS_LIST, nullptr);

#undef ARITH_REWRITER_PARAMS_LIST
