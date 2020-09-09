/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    array_solver.h

Abstract:

    Theory plugin for arrays

Author:

    Nikolaj Bjorner (nbjorner) 2020-09-08

--*/

#include "sat/smt/array_solver.h"

namespace array {
    solver::solver(euf::solver& ctx, theory_id id):
        th_euf_solver(ctx, id),
        a(m),
        m_sort2epsilon(m),
        m_sort2diag(m)
    {}

    bool solver::is_external(bool_var v) { return true; }
    bool solver::propagate(literal l, sat::ext_constraint_idx idx) { return false; }
    void solver::get_antecedents(literal l, sat::ext_justification_idx idx, literal_vector & r, bool probing) {}
    void solver::asserted(literal l) {}
    sat::check_result solver::check() {
        return sat::CR_DONE;
    }
    void solver::push() {
        th_euf_solver::lazy_push();
    }
    void solver::pop(unsigned n) {
        n = lazy_pop(n);        
    }
    std::ostream& solver::display(std::ostream& out) const { return out; }
    std::ostream& solver::display_justification(std::ostream& out, sat::ext_justification_idx idx) const { return out; }
    std::ostream& solver::display_constraint(std::ostream& out, sat::ext_constraint_idx idx) const { return out; }
    void solver::collect_statistics(statistics& st) const {}
    euf::th_solver* solver::fresh(sat::solver* s, euf::solver& ctx) { return nullptr; }
    void solver::new_eq_eh(euf::th_eq const& eq) {}
    bool solver::unit_propagate() { return false; }
    void solver::add_value(euf::enode* n, expr_ref_vector& values) {}
    sat::literal solver::internalize(expr* e, bool sign, bool root, bool learned) { return sat::null_literal;  }
    void solver::internalize(expr* e, bool redundant) {}
    euf::theory_var solver::mk_var(euf::enode* n) {
        return th_euf_solver::mk_var(n);
    }
    void solver::apply_sort_cnstr(euf::enode * n, sort * s) {}        

}
