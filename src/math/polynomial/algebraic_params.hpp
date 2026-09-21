/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    algebraic_params.hpp

Abstract:

    Parameters for the 'algebraic' module.

--*/
#pragma once

#include "util/params.h"
#include "util/gparams.h"

#define ALGEBRAIC_PARAMS_LIST(UINT_, BOOL_, DOUBLE_, STRING_, SYMBOL_) \
  UINT_(zero_accuracy,       "zero_accuracy",       0,     "one of the most time-consuming operations in the real algebraic number module is determining the sign of a polynomial evaluated at a sample point with non-rational algebraic number values. Let k be the value of this option. If k is 0, Z3 uses precise computation. Otherwise, the result of a polynomial evaluation is considered to be 0 if Z3 can show it is inside the interval (-1/2^k, 1/2^k)") \
  UINT_(min_mag,             "min_mag",             16,    "Z3 represents algebraic numbers using a (square-free) polynomial p and an isolating interval (which contains one and only one root of p). This interval may be refined during the computations. This parameter specifies whether to cache the value of a refined interval or not. It says the minimal size of an interval for caching purposes is 1/2^16") \
  BOOL_(factor,              "factor",              true,  "use polynomial factorization to simplify polynomials representing algebraic numbers") \
  UINT_(factor_max_prime,    "factor_max_prime",    31,    "parameter for the polynomial factorization procedure in the algebraic number module. Z3 polynomial factorization is composed of three steps: factorization in GF(p), lifting and search. This parameter limits the maximum prime number p to be used in the first step") \
  UINT_(factor_num_primes,   "factor_num_primes",   1,     "parameter for the polynomial factorization procedure in the algebraic number module. Z3 polynomial factorization is composed of three steps: factorization in GF(p), lifting and search. The search space may be reduced by factoring the polynomial in different GF(p)'s. This parameter specify the maximum number of finite factorizations to be considered, before lifting and searching") \
  UINT_(factor_search_size,  "factor_search_size",  5000,  "parameter for the polynomial factorization procedure in the algebraic number module. Z3 polynomial factorization is composed of three steps: factorization in GF(p), lifting and search. This parameter can be used to limit the search space")

Z3_DEFINE_MODULE_PARAMS(algebraic_params, "algebraic", ALGEBRAIC_PARAMS_LIST);

/*
   REG_MODULE_PARAMS('algebraic', 'algebraic_params::collect_param_descrs')
   REG_MODULE_DESCRIPTION('algebraic', 'real algebraic number package. Non-default parameter settings are not supported')
*/

#undef ALGEBRAIC_PARAMS_LIST
