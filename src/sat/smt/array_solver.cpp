/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    array_solver.h

Abstract:

    Theory plugin for arrays

Author:

    Nikolaj Bjorner (nbjorner) 2020-09-08

--*/

#include "ast/ast_ll_pp.h"
#include "sat/smt/array_solver.h"
#include "sat/smt/euf_solver.h"

namespace array {

    solver::solver(euf::solver& ctx, theory_id id):
        th_euf_solver(ctx, id),
        a(m),
        m_sort2epsilon(m),
        m_sort2diag(m),
        m_find(*this),
        m_hash(*this),
        m_eq(*this),
        m_axioms(DEFAULT_HASHTABLE_INITIAL_CAPACITY, m_hash, m_eq)
    {
        m_constraint = alloc(sat::constraint_base);
        m_constraint->initialize(m_constraint.get(), this);
    }

    sat::check_result solver::check() {
        flet<bool> _is_redundant(m_is_redundant, true);
        bool turn[2] = { false, false };
        turn[s().rand()(2)] = true;
        for (unsigned idx = 0; idx < 2; ++idx) {
            if (turn[idx]) {
                if (add_delayed_axioms())
                    return sat::CR_CONTINUE;
            }
            else {
                if (add_interface_equalities())
                    return sat::CR_CONTINUE;
            }
        }
        return sat::CR_DONE;
    }

    void solver::push() {
        th_euf_solver::lazy_push();
    }

    void solver::pop(unsigned n) {
        n = lazy_pop(n);    
        if (n == 0)
            return;
        m_var_data.resize(get_num_vars());
    }

    std::ostream& solver::display(std::ostream& out) const { 
        for (unsigned i = 0; i < get_num_vars(); ++i) {
            out << var2enode(i)->get_owner_id() << " " << mk_bounded_pp(var2expr(i), m, 2) << "\n";
        }
        return out; 
    }

    std::ostream& solver::display_justification(std::ostream& out, sat::ext_justification_idx idx) const { return out; }
    std::ostream& solver::display_constraint(std::ostream& out, sat::ext_constraint_idx idx) const { return out; }

    void solver::collect_statistics(statistics& st) const {
        st.update("array store", m_stats.m_num_store_axiom);
        st.update("array sel/store", m_stats.m_num_select_store_axiom);
        st.update("array sel/const", m_stats.m_num_select_const_axiom);
        st.update("array sel/map", m_stats.m_num_select_map_axiom);
        st.update("array sel/as array", m_stats.m_num_select_as_array_axiom);
        st.update("array def/map", m_stats.m_num_default_map_axiom);
        st.update("array def/const", m_stats.m_num_default_const_axiom);
        st.update("array def/store", m_stats.m_num_default_store_axiom);
        st.update("array ext ax", m_stats.m_num_extensionality_axiom);
        st.update("array cong ax", m_stats.m_num_congruence_axiom);
        st.update("array exp ax2", m_stats.m_num_select_store_axiom_delayed);
        st.update("array splits", m_stats.m_num_eq_splits);
    }

    euf::th_solver* solver::fresh(sat::solver* s, euf::solver& ctx) {        
        auto* result = alloc(solver, ctx, get_id());
        ast_translation tr(m, ctx.get_manager());
        for (unsigned i = 0; i < get_num_vars(); ++i) {
            expr* e1 = var2expr(i);
            expr* e2 = tr(e1);
            euf::enode* n = ctx.get_enode(e2);
            result->mk_var(n);
        }
        return result; 
    }

    void solver::new_eq_eh(euf::th_eq const& eq) {
        m_find.merge(eq.m_v1, eq.m_v2);
    }

    bool solver::unit_propagate() { 
        if (m_qhead == m_axiom_trail.size())
            return false;
        bool prop = false;
        ctx.push(value_trail<euf::solver, unsigned>(m_qhead));
        for (; m_qhead < m_axiom_trail.size() && !s().inconsistent(); ++m_qhead) 
            if (assert_axiom(m_qhead))
                prop = true;        
        return prop;
    }

    void solver::add_value(euf::enode* n, expr_ref_vector& values) {
        NOT_IMPLEMENTED_YET();
    }

    void solver::merge_eh(theory_var v1, theory_var v2, theory_var u, theory_var v) {
        SASSERT(v1 == find(v1));
        // parents(v2) is a suffix of parents(v1) in the egraph
        // add new axioms for the updated parent/child relations.
        euf::enode* n1 = var2enode(v1);
        euf::enode* n2 = var2enode(v2);
        if (a.is_array(n1->get_owner()))
            for (euf::enode* parent : euf::enode_parents(n2)) 
                add_parent(n1, parent);
        if (is_lambda(n1->get_owner()) || is_lambda(n2->get_owner()))
            push_axiom(congruence_axiom(n1, n2));
    }

    void solver::add_parent(euf::enode* child, euf::enode* parent) {
        SASSERT(parent->is_root());
        var_data& d = get_var_data(child);
        euf::enode* r = child->get_root();
        expr* p = parent->get_owner();
        expr* c = child->get_owner();
        if (a.is_select(p) && parent->get_arg(0)->get_root() == r) {
            if (a.is_const(c) || a.is_as_array(c) || a.is_store(c) || is_lambda(c))
                push_axiom(select_axiom(parent, child));
        }       
        else if (a.mk_default(p)) {
            if (a.is_const(c) || a.is_store(c) || a.is_map(c) || a.is_as_array(c))
                push_axiom(default_axiom(child));
        }
    }

}
