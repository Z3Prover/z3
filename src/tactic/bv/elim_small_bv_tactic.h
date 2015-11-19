/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    elim_small_bv.h

Abstract:

    Tactic that eliminates small, quantified bit-vectors.

Author:

    Christoph (cwinter) 2015-11-09

Revision History:

--*/
#ifndef ELIM_SMALL_BV_H_
#define ELIM_SMALL_BV_H_

#include"params.h"
class ast_manager;
class tactic;

tactic * mk_elim_small_bv_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
    ADD_TACTIC("elim-small-bv", "eliminate small, quantified bit-vectors by expansion.", "mk_elim_small_bv_tactic(m, p)")
*/

#endif
