/*++
Copyright (c) 2016 Microsoft Corporation

Module Name:

    dt2bv_tactic.h

Abstract:

    Tactic that eliminates finite domain data-types.

Author:

    nbjorner 2016-07-22

Revision History:

--*/
#pragma once

#include "util/params.h"
#include "util/obj_hashtable.h"
class ast_manager;
class tactic;

tactic * mk_dt2bv_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
    ADD_TACTIC("dt2bv", "eliminate finite domain data-types. Replace by bit-vectors.", "mk_dt2bv_tactic(m, p)")
*/

