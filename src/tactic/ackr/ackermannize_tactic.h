/*++
Copyright (c) 2016 Microsoft Corporation

Module Name:

ackermannize_tactic.h

Abstract:

Author:

Mikolas Janota

Revision History:
--*/

#ifndef _ACKERMANNIZE_TACTIC_H_
#define _ACKERMANNIZE_TACTIC_H
#include"tactical.h"

tactic * mk_ackermannize_bounded_tactic(ast_manager & m, params_ref const & p);
tactic * mk_ackermannize_tactic(ast_manager & m, params_ref const & p);

/*
  ADD_TACTIC("ackermannize", "A tactic for performing full Ackermannization.", "mk_ackermannize_tactic(m, p)")
  ADD_TACTIC("ackermannize_bounded", "A tactic for performing full Ackermannization where Ackermannization is invoked only if bounds given by the parameters of the tactic are not exceeded.", "mk_ackermannize_bounded_tactic(m, p)")
*/

#endif

