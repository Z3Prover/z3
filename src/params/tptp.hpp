/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    tptp.hpp

Abstract:

    Parameters for the 'tptp' module.

--*/
#pragma once

#include "util/params.h"
#include "util/gparams.h"

#define TPTP_LIST(UINT_, BOOL_, DOUBLE_, STRING_, SYMBOL_) \
  SYMBOL_(root,                   "root",                   "",     "root directory for resolving TPTP include() axiom paths (replaces the TPTP environment variable)") \
  SYMBOL_(dump_smt2,              "dump_smt2",              "",     "if non-empty, file path to dump the parsed TPTP goal as an SMT-LIB2 benchmark (replaces the Z3_TPTP_DUMP_SMT2 environment variable)") \
  BOOL_  (unfold_lambda_macros,   "unfold_lambda_macros",   true,   "pre-process the goal by unfolding constants that are defined as lambda terms (shallow embeddings of higher-order/modal operators), inlining and beta-reducing their occurrences") \
  BOOL_  (leibniz_instantiation,  "leibniz_instantiation",  false,  "pre-process the goal by synthesizing and adding Leibniz-equality style instantiations of universally quantified predicate variables applied to distinct argument terms")

Z3_DEFINE_MODULE_PARAMS(tptp, "tptp", TPTP_LIST);

/*
   REG_MODULE_PARAMS('tptp', 'tptp::collect_param_descrs')
   REG_MODULE_DESCRIPTION('tptp', 'TPTP frontend parameters')
*/

#undef TPTP_LIST
