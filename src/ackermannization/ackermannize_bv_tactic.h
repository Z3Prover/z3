/*++
Copyright (c) 2016 Microsoft Corporation

Module Name:

ackermannize_bv_tactic.h

Abstract:

Author:

Mikolas Janota

Revision History:
--*/

#pragma once
#include "tactic/tactical.h"

tactic * mk_ackermannize_bv_tactic(ast_manager & m, params_ref const & p);

/*
  ADD_TACTIC("ackermannize_bv", "A tactic for performing full Ackermannization on bv instances.", "mk_ackermannize_bv_tactic(m, p)")
*/


