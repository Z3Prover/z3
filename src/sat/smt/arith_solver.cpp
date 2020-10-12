/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    arith_solver.cpp

Abstract:

    Theory plugin for arithmetic

Author:

    Nikolaj Bjorner (nbjorner) 2020-09-08

--*/

#include "sat/smt/euf_solver.h"
#include "sat/smt/arith_solver.h"


namespace arith {

    solver::solver(euf::solver& ctx, theory_id id):
        th_euf_solver(ctx, symbol("arith"), id),
        a(m)
    {}

    solver::~solver() {}

    void solver::asserted(literal l) {}
    sat::check_result solver::check() { return sat::check_result::CR_DONE; }
    
    euf::th_solver* solver::clone(sat::solver* s, euf::solver& ctx) { return nullptr;}
    void solver::new_eq_eh(euf::th_eq const& eq) {}
    bool solver::unit_propagate() { return false; }
    void solver::add_value(euf::enode* n, model& mdl, expr_ref_vector& values) {}
    void solver::add_dep(euf::enode* n, top_sort<euf::enode>& dep) {}
}
