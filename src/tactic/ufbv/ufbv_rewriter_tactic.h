/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    ufbv_rewriter_tactic.cpp

Abstract:

    UFBV Rewriter (demodulator)

Author:

    Christoph (cwinter) 2012-10-26

Notes:

--*/
#pragma once

#include "util/params.h"
#include "tactic/tactic.h"
class ast_manager;
class tactic;

tactic * mk_ufbv_rewriter_tactic(ast_manager & m, params_ref const & p = params_ref());

Z3_ADD_TACTIC(ufbv_rewriter, "ufbv-rewriter", "Applies UFBV-specific rewriting rules, mainly demodulation.", mk_ufbv_rewriter_tactic(m, p));

