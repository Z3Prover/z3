/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    mip_tactic.h

Abstract:

    Tactic for solvig MIP (mixed integer) problem.
    This is a temporary tactic. It should be deleted
    after theory_arith is upgraded.

Author:

    Leonardo (leonardo) 2012-02-26

Notes:

--*/
#ifndef _MIP_TACTIC_H_
#define _MIP_TACTIC_H_

#include"params.h"
class ast_manager;
class tactic;

tactic * mk_mip_tactic(ast_manager & m, params_ref const & p = params_ref());

#endif
