/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    fpa_rewriter_params.hpp

Abstract:

    Parameters for the 'rewriter' module.

--*/
#pragma once

#include "util/params.h"
#include "util/gparams.h"

#define FPA_REWRITER_PARAMS_LIST(UINT_, BOOL_, DOUBLE_, STRING_, SYMBOL_) \
  BOOL_(hi_fp_unspecified,  "hi_fp_unspecified",  false,  "use the 'hardware interpretation' for unspecified values in fp.to_ubv, fp.to_sbv, fp.to_real, and fp.to_ieee_bv")

Z3_DEFINE_MODULE_PARAMS(fpa_rewriter_params, "rewriter", FPA_REWRITER_PARAMS_LIST);

/*
   REG_MODULE_PARAMS('rewriter', 'fpa_rewriter_params::collect_param_descrs')
*/

#undef FPA_REWRITER_PARAMS_LIST
