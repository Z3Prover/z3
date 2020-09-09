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
        m_sort2diag(m),
        m_find(*this)
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

    void solver::merge_eh(theory_var v1, theory_var v2, theory_var u, theory_var v) {
        SASSERT(v1 == find(v1));
        // parents(v2) is a suffix of parents(v1) in the egraph
        // add new axioms for the updated parent/child relations.
        euf::enode* n1 = var2enode(v1);
        euf::enode* n2 = var2enode(v2);
        for (euf::enode* parent : euf::enode_parents(n2)) 
            add_parent(n1, parent);
    }

    void solver::add_parent(euf::enode* child, euf::enode* parent) {
        SASSERT(parent->is_root());
        var_data& d = get_var_data(child);
        euf::enode* r = child->get_root();
        expr* p = parent->get_owner();
        expr* c = child->get_owner();
        if (a.is_select(p) && parent->get_arg(0)->get_root() == r) {
            if (a.is_const(c) || a.is_as_array(c) || a.is_store(c))
                push_axiom(select_axiom(parent, child));
        }       
        else if (a.mk_default(p)) {
            if (a.is_const(c) || a.is_store(c) || a.is_map(c) || a.is_as_array(c))
                push_axiom(default_axiom(child));
        }
    }

}
