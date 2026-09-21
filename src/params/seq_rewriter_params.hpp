/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    seq_rewriter_params.hpp

Abstract:

    Parameters for the 'rewriter' module.

--*/
#pragma once

#include "util/params.h"
#include "util/gparams.h"

#define SEQ_REWRITER_PARAMS_LIST(UINT_, BOOL_, DOUBLE_, STRING_, SYMBOL_) \
  BOOL_(coalesce_chars,       "coalesce_chars",       true,  "coalesce characters into strings") \
  UINT_(max_power_expansion,  "max_power_expansion",  2,     "maximal exponent of a sequence power that is expanded into a concatenation")

Z3_DEFINE_MODULE_PARAMS(seq_rewriter_params, "rewriter", SEQ_REWRITER_PARAMS_LIST);

/*
   REG_MODULE_PARAMS('rewriter', 'seq_rewriter_params::collect_param_descrs')
*/

#undef SEQ_REWRITER_PARAMS_LIST
