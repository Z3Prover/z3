/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    pp_params.hpp

Abstract:

    Parameters for the 'pp' module.

--*/
#pragma once

#include "util/params.h"
#include "util/gparams.h"

#define PP_PARAMS_LIST(UINT_, BOOL_, DOUBLE_, STRING_, SYMBOL_) \
  UINT_(max_indent,         "max_indent",         UINT_MAX,  "max. indentation in pretty printer") \
  UINT_(max_num_lines,      "max_num_lines",      UINT_MAX,  "max. number of lines to be displayed in pretty printer") \
  UINT_(max_width,          "max_width",          80,        "max. width in pretty printer") \
  UINT_(max_ribbon,         "max_ribbon",         80,        "max. ribbon (width - indentation) in pretty printer") \
  UINT_(max_depth,          "max_depth",          5,         "max. term depth (when pretty printing SMT2 terms/formulas)") \
  BOOL_(no_lets,            "no_lets",            false,     "dont print lets in low level SMT printer") \
  UINT_(min_alias_size,     "min_alias_size",     10,        "min. size for creating an alias for a shared term (when pretty printing SMT2 terms/formulas)") \
  BOOL_(decimal,            "decimal",            false,     "pretty print real numbers using decimal notation (the output may be truncated). Z3 adds a ? if the value is not precise") \
  UINT_(decimal_precision,  "decimal_precision",  10,        "maximum number of decimal places to be used when pp.decimal=true") \
  BOOL_(bv_literals,        "bv_literals",        true,      "use Bit-Vector literals (e.g, #x0F and #b0101) during pretty printing") \
  BOOL_(fp_real_literals,   "fp_real_literals",   false,     "use real-numbered floating point literals (e.g, +1.0p-1) during pretty printing") \
  BOOL_(bv_neg,             "bv_neg",             false,     "use bvneg when displaying Bit-Vector literals where the most significant bit is 1") \
  BOOL_(flat_assoc,         "flat_assoc",         true,      "flat associative operators (when pretty printing SMT2 terms/formulas)") \
  BOOL_(fixed_indent,       "fixed_indent",       false,     "use a fixed indentation for applications") \
  BOOL_(single_line,        "single_line",        false,     "ignore line breaks when true") \
  BOOL_(bounded,            "bounded",            false,     "ignore characters exceeding max width") \
  BOOL_(pretty_proof,       "pretty_proof",       false,     "use slower, but prettier, printer for proofs") \
  BOOL_(simplify_implies,   "simplify_implies",   true,      "simplify nested implications for pretty printing")

Z3_DEFINE_MODULE_PARAMS(pp_params, "pp", PP_PARAMS_LIST);

/*
   REG_MODULE_PARAMS('pp', 'pp_params::collect_param_descrs')
   REG_MODULE_DESCRIPTION('pp', 'pretty printer')
*/

#undef PP_PARAMS_LIST
