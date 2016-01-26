/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

lackr_tactic.h

Abstract:

Author:

Mikolas Janota

Revision History:
--*/

#ifndef _LACKR_TACTIC_H_
#define _LACKR_TACTIC_H_
#include"tactical.h"

tactic * mk_lackr_tactic(ast_manager & m, params_ref const & p);

/*
ADD_TACTIC("lackr", "A tactic for solving QF_UFBV based on Ackermannization.", "mk_lackr_tactic(m, p)")
*/

#endif

