/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    fpa2bv_lazy_tactic.h

Abstract:

    Tactic that converts floating points to bit-vectors lazily

Author:

    Aleksander Zeljic 2012-11-15

Notes:

--*/
#ifndef _FPA2BV_APPROX_TACTIC_
#define _FPA2BV_APPROX_TACTIC_

#include"params.h"
class ast_manager;
class tactic;



tactic * mk_fpa2bv_approx_tactic(ast_manager & m, params_ref const & p = params_ref());
/*
  ADD_TACTIC("fpa2bv_approx", "An iterative approximation based bit-blasting decision procedure for FPA.", "mk_fpa2bv_approx_tactic(m, p)")
*/

#endif
