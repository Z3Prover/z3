/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    qfuf_tactic.h

Abstract:

    Tactic for QF_QFUF benchmarks.

Author:

    Leonardo de Moura (leonardo) 2012-02-21


Notes:

--*/
#pragma once

#include "util/params.h"
#include "tactic/tactic.h"
class ast_manager;
class tactic;

tactic * mk_qfuf_tactic(ast_manager & m, params_ref const & p);

Z3_ADD_TACTIC(qfuf, "qfuf", "builtin strategy for solving QF_UF problems.", mk_qfuf_tactic(m, p));

