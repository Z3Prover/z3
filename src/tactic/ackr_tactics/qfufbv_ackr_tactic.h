/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

qfufbv_ackr_tactic.h

Abstract:

Author:

Mikolas Janota

Revision History:
--*/

#ifndef _QFUFBV_ACKR_TACTIC_H_
#define _QFUFBV_ACKR_TACTIC_H_
#include"tactical.h"

tactic * mk_qfufbv_ackr_tactic(ast_manager & m, params_ref const & p);

/*
ADD_TACTIC("qfufbv_ackr", "A tactic for solving QF_UFBV based on Ackermannization.", "mk_qfufbv_ackr_tactic(m, p)")
*/

#endif

