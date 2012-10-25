/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    elim_uncnstr_tactic.h

Abstract:

    Eliminated applications containing unconstrained variables.

Author:

    Leonardo (leonardo) 2011-10-22

Notes:

--*/
#ifndef _ELIM_UNCNSTR_TACTIC_H_
#define _ELIM_UNCNSTR_TACTIC_H_

#include"params.h"

class tactic;
class ast_manager;

tactic * mk_elim_uncnstr_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
  ADD_TACTIC("elim-uncnstr", "eliminate application containing unconstrained variables.", "mk_elim_uncnstr_tactic(m, p)")
*/
#endif

