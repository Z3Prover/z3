/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    qflia_tactic.h

Abstract:

    Tactic for QF_LIA

Author:

    Leonardo (leonardo) 2012-02-26

Notes:

--*/
#pragma once

#include "util/params.h"
#include "tactic/probe.h"
#include "tactic/tactic.h"
class ast_manager;
class tactic;

tactic * mk_preamble_tactic(ast_manager& m);

tactic * mk_qflia_tactic(ast_manager & m, params_ref const & p = params_ref());
Z3_ADD_TACTIC(qflia, "qflia", "builtin strategy for solving QF_LIA problems.", mk_qflia_tactic(m, p));


probe * mk_is_quasi_pb_probe();

Z3_ADD_PROBE(is_quasi_pb, "is-quasi-pb", "true if the goal is quasi-pb.", mk_is_quasi_pb_probe());

