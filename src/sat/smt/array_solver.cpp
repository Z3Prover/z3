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
            out << var2enode(i)->get_expr_id() << " " << mk_bounded_pp(var2expr(i), m, 2) << "\n";
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

    void solver::merge_eh(theory_var v1, theory_var v2, theory_var, theory_var) {
        euf::enode* n1 = var2enode(v1);
        euf::enode* n2 = var2enode(v2);
        SASSERT(n1->get_root() == n2->get_root());
        SASSERT(n1->is_root() || n2->is_root());
        SASSERT(v1 == find(v1));

        expr* e1 = n1->get_expr();
        expr* e2 = n2->get_expr();
        auto& d1 = get_var_data(v1);
        auto& d2 = get_var_data(v2);
        if (d2.m_prop_upward && !d1.m_prop_upward) 
            set_prop_upward(v1);
        if (a.is_array(e1))
            for (euf::enode* parent : d2.m_parents) {
                add_parent(v1, parent);
                if (a.is_store(parent->get_expr()))
                    add_store(v1, parent);
            }
        if (is_lambda(e1) || is_lambda(e2))
            push_axiom(congruence_axiom(n1, n2));
    }

    void solver::unmerge_eh(theory_var v1, theory_var v2) {
        auto& p1 = get_var_data(v1).m_parents;
        auto& p2 = get_var_data(v2).m_parents;
        p1.shrink(p1.size() - p2.size());
    }

    void solver::add_store(theory_var v, euf::enode* store) {
        SASSERT(a.is_store(store->get_expr()));
        auto& d = get_var_data(v);
        unsigned lambda_equiv_class_size = get_lambda_equiv_size(d);
        if (get_config().m_array_always_prop_upward || lambda_equiv_class_size >= 1) 
            set_prop_upward(d);
        for (euf::enode* n : d.m_parents)
            if (a.is_select(n->get_expr()))
                push_axiom(select_axiom(n, store));
        if (get_config().m_array_always_prop_upward || lambda_equiv_class_size >= 1)
            set_prop_upward(store);
    }

    void solver::add_parent(theory_var v_child, euf::enode* parent) {
        SASSERT(parent->is_root());
        get_var_data(v_child).m_parents.push_back(parent);
        euf::enode* child = var2enode(v_child);
        euf::enode* r = child->get_root();
        expr* p = parent->get_expr();
        expr* c = child->get_expr();
        if (a.is_select(p) && parent->get_arg(0)->get_root() == r) {
            if (a.is_const(c) || a.is_as_array(c) || a.is_store(c) || is_lambda(c)) 
                push_axiom(select_axiom(parent, child));   
#if 0
            if (!get_config().m_array_delay_exp_axiom && d.m_prop_upward) {
                auto& d = get_var_data(v_child);
                for (euf::enode* p2 : d.m_parents)
                    if (a.is_store(p2->get_expr()))
                        push_axiom(select_axiom(parent, p2));
            }
#endif
        }       
        else if (a.mk_default(p)) {
            if (a.is_const(c) || a.is_store(c) || a.is_map(c) || a.is_as_array(c)) 
                push_axiom(default_axiom(child));
        }
    }

    void solver::set_prop_upward(theory_var v) {
        auto& d = get_var_data(find(v));
        if (!d.m_prop_upward) {
            ctx.push(reset_flag_trail<euf::solver>(d.m_prop_upward));
            d.m_prop_upward = true;
            if (!get_config().m_array_delay_exp_axiom)
                push_parent_select_store_axioms(v);
            set_prop_upward(d);
        }
    }

    void solver::set_prop_upward(euf::enode* n) {
        if (a.is_store(n->get_expr()))
            set_prop_upward(n->get_arg(0)->get_th_var(get_id()));
    }

    void solver::set_prop_upward(var_data& d) {
        for (auto* p : d.m_parents)
            set_prop_upward(p);
    }

    /**
       \brief Return the size of the equivalence class for array terms 
              that can be expressed as \lambda i : Index . [.. (select a i) ..]
     */
    unsigned solver::get_lambda_equiv_size(var_data const& d) {
        unsigned sz = 0;
        for (auto* p : d.m_parents)
            if (a.is_store(p->get_expr()))
                ++sz;
        return sz;
    }



}
