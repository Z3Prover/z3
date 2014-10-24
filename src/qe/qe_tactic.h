/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    qe_tactic.h

Abstract:

    Quantifier elimination front-end for tactic framework.

Author:

    Leonardo de Moura (leonardo) 2011-12-28.

Revision History:

--*/
#ifndef _QE_TACTIC_H_
#define _QE_TACTIC_H_

#include"params.h"
class ast_manager;
class tactic;

tactic * mk_qe_tactic(ast_manager & m, params_ref const & p = params_ref());
/*
  ADD_TACTIC("qe", "apply quantifier elimination.", "mk_qe_tactic(m, p)")
*/
#endif
