/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    arith_axioms.cpp

Abstract:

    Theory plugin for arithmetic

Author:

    Nikolaj Bjorner (nbjorner) 2020-09-08

--*/
#pragma once

#include "sat/smt/euf_solver.h"
#include "sat/smt/arith_solver.h"


namespace arith {

    // q = 0 or q * (p div q) = p
    void solver::mk_div_axiom(expr* p, expr* q) {
        if (a.is_zero(q)) return;
        literal eqz = eq_internalize(q, a.mk_real(0));
        literal eq  = eq_internalize(a.mk_mul(q, a.mk_div(p, q)), p);
        add_clause(eqz, eq);
    }


}
