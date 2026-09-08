/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    bool_rewriter_params.hpp

Abstract:

    Parameters for the 'rewriter' module.

--*/
#pragma once

#include "util/params.h"
#include "util/gparams.h"

#define BOOL_REWRITER_PARAMS_LIST(UINT_, BOOL_, DOUBLE_, STRING_, SYMBOL_) \
  BOOL_(ite_extra_rules,           "ite_extra_rules",           true,      "extra ite simplifications, these additional simplifications may reduce size locally but increase globally") \
  BOOL_(flat,                      "flat",                      true,      "create nary applications for +,*,bvadd,bvmul,bvand,bvor,bvxor") \
  BOOL_(flat_and_or,               "flat_and_or",               true,      "create nary applications for and,or") \
  BOOL_(sort_disjunctions,         "sort_disjunctions",         true,      "sort subterms in disjunctions") \
  BOOL_(elim_and,                  "elim_and",                  false,     "conjunctions are rewritten using negation and disjunctions") \
  BOOL_(elim_ite,                  "elim_ite",                  true,      "eliminate ite in favor of and/or") \
  BOOL_(local_ctx,                 "local_ctx",                 false,     "perform local (i.e., cheap) context simplifications") \
  UINT_(local_ctx_limit,           "local_ctx_limit",           UINT_MAX,  "limit for applying local context simplifier") \
  BOOL_(blast_distinct,            "blast_distinct",            false,     "expand a distinct predicate into a quadratic number of disequalities") \
  UINT_(blast_distinct_threshold,  "blast_distinct_threshold",  UINT_MAX,  "when blast_distinct is true, only distinct expressions with less than this number of arguments are blasted")

Z3_DEFINE_MODULE_PARAMS(bool_rewriter_params, "rewriter", BOOL_REWRITER_PARAMS_LIST);

/*
   REG_MODULE_PARAMS('rewriter', 'bool_rewriter_params::collect_param_descrs')
*/

#undef BOOL_REWRITER_PARAMS_LIST
