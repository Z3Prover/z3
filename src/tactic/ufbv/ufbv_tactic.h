/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    ufbv_tactic.h

Abstract:

    General purpose tactic for UFBV benchmarks.

Author:

    Christoph (cwinter) 2012-10-24

Notes:

--*/
#pragma once

#include "util/params.h"
class ast_manager;
class tactic;

tactic * mk_ufbv_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
  ADD_TACTIC("bv",  "builtin strategy for solving BV problems (with quantifiers).", "mk_ufbv_tactic(m, p)")
  ADD_TACTIC("ufbv",  "builtin strategy for solving UFBV problems (with quantifiers).", "mk_ufbv_tactic(m, p)")
*/

