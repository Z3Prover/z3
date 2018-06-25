#pragma once
/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    qffplra_tactic.h

Abstract:

    Tactic for QF_FPLRA benchmarks.

Author:

    Christoph (cwinter) 2018-04-24

Notes:


--*/
#ifndef QFFPLRA_TACTIC_H_
#define QFFPLRA_TACTIC_H_

#include "util/params.h"
class ast_manager;
class tactic;

tactic * mk_qffplra_tactic(ast_manager & m, params_ref const & p = params_ref());
/*
ADD_TACTIC("qffplra", "(try to) solve goal using the tactic for QF_FPLRA.", "mk_qffplra_tactic(m, p)")
*/

probe * mk_is_qffplra_probe();
/*
ADD_PROBE("is-qffplra", "true if the goal is in QF_FPLRA.", "mk_is_qffplra_probe()")
*/

#endif
