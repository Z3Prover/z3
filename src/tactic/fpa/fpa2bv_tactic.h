/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    fpa2bv_tactic.h

Abstract:

    Tactic that converts floating points to bit-vectors

Author:

    Christoph (cwinter) 2012-02-09

Notes:

--*/
#ifndef _FPA2BV_TACTIC_
#define _FPA2BV_TACTIC_

#include"params.h"
class ast_manager;
class tactic;

tactic * mk_fpa2bv_tactic(ast_manager & m, params_ref const & p = params_ref());
/*
  ADD_TACTIC("fpa2bv", "convert floating point numbers to bit-vectors.", "mk_fpa2bv_tactic(m, p)")
*/

#endif
