/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    qfufbv_tactic.h

Abstract:

    Tactic for QF_UFBV

Author:

    Leonardo (leonardo) 2012-02-27

Notes:

--*/
#ifndef QFUFBV_TACTIC_H_
#define QFUFBV_TACTIC_H_

#include "util/params.h"
class ast_manager;
class tactic;

tactic * mk_qfufbv_tactic(ast_manager & m, params_ref const & p = params_ref());

tactic * mk_qfufbv_ackr_tactic(ast_manager & m, params_ref const & p);

/*
  ADD_TACTIC("qfufbv", "builtin strategy for solving QF_UFBV problems.", "mk_qfufbv_tactic(m, p)")
  ADD_TACTIC("qfufbv_ackr", "A tactic for solving QF_UFBV based on Ackermannization.", "mk_qfufbv_ackr_tactic(m, p)")
*/

#endif
