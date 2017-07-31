/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    qfnia_tactic.h

Abstract:

    Tactic for QF_NIA

Author:

    Leonardo (leonardo) 2012-02-28

Notes:

--*/
#ifndef QFNIA_TACTIC_H_
#define QFNIA_TACTIC_H_

#include "util/params.h"
class ast_manager;
class tactic;

tactic * mk_qfnia_tactic(ast_manager & m, params_ref const & p = params_ref());
/*
  ADD_TACTIC("qfnia", "builtin strategy for solving QF_NIA problems.", "mk_qfnia_tactic(m, p)")
*/

#endif
