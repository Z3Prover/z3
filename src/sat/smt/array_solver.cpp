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

    solver::solver(euf::solver& ctx, theory_id id) :
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
            if (turn[idx] && add_delayed_axioms())
                return sat::check_result::CR_CONTINUE;
            else if (!turn[idx] && add_interface_equalities())
                return sat::check_result::CR_CONTINUE;
        }
        return sat::check_result::CR_DONE;
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
            auto& d = get_var_data(i);
            out << var2enode(i)->get_expr_id() << " " << mk_bounded_pp(var2expr(i), m, 2) << "\n";
            display_info(out, "parent stores", d.m_parent_stores);
            display_info(out, "parent select", d.m_parent_selects);
            display_info(out, "parent maps  ", d.m_parent_maps);
            display_info(out, "parent defs  ", d.m_parent_defaults);
            display_info(out, "maps         ", d.m_maps);
            display_info(out, "consts       ", d.m_consts);
            display_info(out, "as-arrays    ", d.m_as_arrays);
        }
        return out;
    }
    std::ostream& solver::display_info(std::ostream& out, char const* id, euf::enode_vector const& v) const {
        if (v.empty())
            return out;
        out << id << ": ";
        for (euf::enode* p : v)
            out << mk_bounded_pp(p->get_expr(), m, 2) << " ";
        out << "\n";
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
        for (euf::enode* store : d2.m_stores)
            add_store(v1, store);
        for (euf::enode* store : d2.m_parent_stores)
            add_parent_store(v1, store);
        for (euf::enode* select : d2.m_parent_selects)            
            add_parent_select(v1, select);
        for (euf::enode* map : d2.m_parent_maps)
            add_parent_map(v1, map);
        for (euf::enode* cnst : d2.m_consts)
            add_const(v1, cnst);
        for (euf::enode* aa : d2.m_as_arrays)
            add_as_array(v1, aa);
        if (is_lambda(e1) || is_lambda(e2))
            push_axiom(congruence_axiom(n1, n2));
    }

    void solver::tracked_push(euf::enode_vector& v, euf::enode* n) {
        v.push_back(n);
        ctx.push(push_back_trail<euf::solver, euf::enode*, false>(v));
    }

    void solver::add_store(theory_var v, euf::enode* store) {
        SASSERT(a.is_store(store->get_expr()));
        auto& d = get_var_data(v);
        if (should_set_prop_upward(d)) 
            set_prop_upward(d);        
        tracked_push(d.m_stores, store);
        if (should_set_prop_upward(d))
            set_prop_upward(store);
        for (euf::enode* select : d.m_parent_selects)
            push_axiom(select_axiom(select, store));
    }

    void solver::add_map(theory_var v, euf::enode* map) {
        SASSERT(a.is_map(map->get_expr()));
        v = find(v);
        auto& d = get_var_data(v);
        set_prop_upward(d);
        tracked_push(d.m_maps, map);
        propagate_select_axioms(d, map);
        set_prop_upward(map);
    }

    void solver::add_as_array(theory_var v, euf::enode* aa) {
        SASSERT(a.is_as_array(aa->get_expr()));
        v = find(v);
        auto& d = get_var_data(v);
        if (should_set_prop_upward(d))
            set_prop_upward(d);
        tracked_push(d.m_as_arrays, aa);
        push_axiom(default_axiom(aa));
        propagate_select_axioms(d, aa);
    }

    void solver::add_const(theory_var v, euf::enode* cnst) {
        v = find(v);
        SASSERT(a.is_const(cnst->get_expr()));
        SASSERT(var2enode(v)->get_root() == cnst->get_root());

        tracked_push(get_var_data(v).m_consts, cnst);
        auto& d = get_var_data(v);
        if (should_set_prop_upward(d)) 
            set_prop_upward(d);
        propagate_select_axioms(d, cnst);
    }

    void solver::add_parent_select(theory_var v_child, euf::enode* select) {
        v_child = find(v_child);
        tracked_push(get_var_data(v_child).m_parent_selects, select);
        euf::enode* child = var2enode(v_child);
        expr* c = child->get_expr();
        SASSERT(a.is_select(select->get_expr()));
        SASSERT(select->get_arg(0)->get_root() == child->get_root());
        if (a.is_const(c) || a.is_as_array(c) || a.is_store(c) || is_lambda(c))
            push_axiom(select_axiom(select, child));
    }

    void solver::add_parent_store(theory_var v_child, euf::enode* store) {
        SASSERT(a.is_store(store->get_expr()));
        SASSERT(store->get_arg(0)->get_root() == var2enode(v_child)->get_root());
        v_child = find(v_child);
        auto& d = get_var_data(v_child);
        tracked_push(d.m_parent_stores, store);
        propagate_select_axioms(d, store);
    }

    void solver::add_parent_map(theory_var v_child, euf::enode* map) {
        SASSERT(a.is_map(map->get_expr()));
        v_child = find(v_child);
        auto& d = get_var_data(v_child);
        tracked_push(d.m_parent_maps, map);
        propagate_select_axioms(d, map);
    }

    void solver::propagate_select_axioms(var_data const& d, euf::enode* a) {
        if (d.m_prop_upward && !get_config().m_array_delay_exp_axiom)
            for (euf::enode* select : d.m_parent_selects)
                push_axiom(select_axiom(select, a));
    }

    void solver::propagate_parent_stores_default(theory_var v) {
        v = find(v);
        auto& d = get_var_data(v);
        for (euf::enode* store : d.m_parent_stores)
            push_axiom(default_axiom(store));
    }

    void solver::add_parent_default(theory_var v, euf::enode* def) {
        SASSERT(a.is_default(def->get_expr()));
        v = find(v);
        auto& d = get_var_data(v);
        for (euf::enode* store : d.m_stores)
            push_axiom(default_axiom(store));
        if (!get_config().m_array_delay_exp_axiom && d.m_prop_upward)             
            propagate_parent_stores_default(v);            
    }

    void solver::propagate_parent_map_axioms(theory_var v) {
        auto& d = get_var_data(v);
        for (auto* n : d.m_parent_maps)
            for (euf::enode* select : d.m_parent_selects)
                push_axiom(select_axiom(select, n));        
    }


    void solver::set_prop_upward(theory_var v) {
        auto& d = get_var_data(find(v));
        if (!d.m_prop_upward) {
            ctx.push(reset_flag_trail<euf::solver>(d.m_prop_upward));
            d.m_prop_upward = true;
            if (!get_config().m_array_delay_exp_axiom) {
                push_parent_select_store_axioms(v);
                propagate_parent_map_axioms(v);
            }
            set_prop_upward(d);
        }
    }

    void solver::set_prop_upward(euf::enode* n) {
        if (a.is_store(n->get_expr()))
            set_prop_upward(n->get_arg(0)->get_th_var(get_id()));
    }

    void solver::set_prop_upward(var_data& d) {
        for (auto* p : d.m_stores)
            set_prop_upward(p);
    }

    /**
       \brief Return the size of the equivalence class for array terms
              that can be expressed as \lambda i : Index . [.. (select a i) ..]
     */
    unsigned solver::get_lambda_equiv_size(var_data const& d) {
        return d.m_parent_selects.size() + 2 * (d.m_maps.size() + d.m_consts.size());
    }

    bool solver::should_set_prop_upward(var_data const& d) {
        return get_config().m_array_always_prop_upward || get_lambda_equiv_size(d) >= 1;
    }
}
