/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    fix_dl_var_tactic.h

Abstract:

    Fix a difference logic variable to 0.
    If the problem is in the difference logic fragment, that is, all arithmetic terms
    are of the form (x + k), and the arithmetic atoms are of the 
    form x - y <= k or x - y = k. Then, we can set one variable to 0.

    This is useful because, many bounds can be exposed after this operation is performed.

Author:

    Leonardo (leonardo) 2011-12-29

Notes:

--*/
#ifndef _FIX_DL_VAR_TACTIC_H_
#define _FIX_DL_VAR_TACTIC_H_

#include"params.h"
class ast_manager;
class tactic;

tactic * mk_fix_dl_var_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
  ADD_TACTIC("fix-dl-var", "if goal is in the difference logic fragment, then fix the variable with the most number of occurrences at 0.", "mk_fix_dl_var_tactic(m, p)")
*/

#endif
