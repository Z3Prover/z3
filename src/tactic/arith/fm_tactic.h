/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    fm_tactic.h

Abstract:

    Use Fourier-Motzkin to eliminate variables.
    This strategy can handle conditional bounds 
    (i.e., clauses with at most one constraint).
    
    The strategy mk_occf can be used to put the
    formula in OCC form.

Author:

    Leonardo de Moura (leonardo) 2012-02-04.

Revision History:

--*/
#pragma once

#include "util/params.h"
class ast_manager;
class tactic;

tactic * mk_fm_tactic(ast_manager & m, params_ref const & p = params_ref());
/*
  ADD_TACTIC("fm", "eliminate variables using fourier-motzkin elimination.", "mk_fm_tactic(m, p)")
*/

