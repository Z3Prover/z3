/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    sat_th.cpp

Abstract:

    Theory plugins

Author:

    Nikolaj Bjorner (nbjorner) 2020-08-25

--*/

#include "sat/smt/sat_th.h"
#include "sat/smt/euf_solver.h"

namespace euf {


    th_euf_solver::th_euf_solver(euf::solver& ctx, euf::theory_id id):
        th_solver(ctx.get_manager(), id),
        ctx(ctx)
    {}

    theory_var th_euf_solver::get_th_var(expr* e) const {
        return get_th_var(ctx.get_enode(e));
    }
    




}
