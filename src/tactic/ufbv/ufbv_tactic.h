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
#include "tactic/tactic.h"
class ast_manager;
class tactic;

tactic * mk_ufbv_tactic(ast_manager & m, params_ref const & p = params_ref());

Z3_ADD_TACTIC(bv, "bv", "builtin strategy for solving BV problems (with quantifiers).", mk_ufbv_tactic(m, p));
Z3_ADD_TACTIC(ufbv, "ufbv", "builtin strategy for solving UFBV problems (with quantifiers).", mk_ufbv_tactic(m, p));

