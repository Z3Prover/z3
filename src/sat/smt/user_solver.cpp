/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    user_solver.cpp

Abstract:

    User propagator plugin.

Author:

    Nikolaj Bjorner (nbjorner) 2020-09-23

--*/

#include "sat/smt/user_solver.h"
#include "sat/smt/euf_solver.h"

namespace user_solver {

    solver::solver(euf::solver& ctx) :
        th_euf_solver(ctx, symbol("user"), ctx.get_manager().mk_family_id("user"))
    {}

    solver::~solver() {
        dealloc(m_api_context);
    }

    void solver::add_expr(expr* e) {
        force_push();
        ctx.internalize(e);
        euf::enode* n = expr2enode(e);
        if (is_attached_to_var(n))
            return;
        euf::theory_var v = mk_var(n);
        ctx.attach_th_var(n, this, v);
        expr_ref r(m);
        sat::literal_vector explain;
        if (ctx.is_fixed(n, r, explain))
            m_prop.push_back(prop_info(explain, v, r));        
    }

    void solver::propagate_cb(
        unsigned num_fixed, expr* const* fixed_ids,
        unsigned num_eqs, expr* const* eq_lhs, expr* const* eq_rhs,
        expr* conseq) {
        m_fixed_ids.reset();
        for (unsigned i = 0; i < num_fixed; ++i)
            m_fixed_ids.push_back(get_th_var(fixed_ids[i]));
        m_prop.push_back(prop_info(num_fixed, m_fixed_ids.data(), num_eqs, eq_lhs, eq_rhs, expr_ref(conseq, m)));
        DEBUG_CODE(validate_propagation(););
    }

    void solver::register_cb(expr* e) {
        add_expr(e);
    }
    
    void solver::next_split_cb(expr* e, unsigned idx, lbool phase) {
        if (e == nullptr) {
            m_next_split_expr = nullptr;
            return;
        }
        force_push();
        ctx.internalize(e);
        m_next_split_expr = e;
        m_next_split_idx = idx;
        m_next_split_phase = phase;
    }

    sat::check_result solver::check() {
        if (!(bool)m_final_eh)
            return  sat::check_result::CR_DONE;
        unsigned sz = m_prop.size();
        m_final_eh(m_user_context, this);
        return sz == m_prop.size() ? sat::check_result::CR_DONE : sat::check_result::CR_CONTINUE;
    }

    void solver::new_fixed_eh(euf::theory_var v, expr* value, unsigned num_lits, sat::literal const* jlits) {
        if (!m_fixed_eh)
            return;
        force_push();
        m_id2justification.setx(v, sat::literal_vector(num_lits, jlits), sat::literal_vector());
        m_fixed_eh(m_user_context, this, var2expr(v), value);
    }
    
    bool solver::decide(sat::bool_var& var, lbool& phase) {
        
        if (!m_decide_eh)
            return false;
        
        euf::enode* original_enode = bool_var2enode(var);
        
        if (!is_attached_to_var(original_enode))
            return false;
        
        unsigned new_bit = 0; // ignored; currently no bv-support
        expr* e = bool_var2expr(var);
        
        m_decide_eh(m_user_context, this, &e, &new_bit, &phase);
        
        euf::enode* new_enode = ctx.get_enode(e);
    
        if (original_enode == new_enode)
            return false;
        
        var = new_enode->bool_var();
        return true;
    }
    
    bool solver::get_case_split(sat::bool_var& var, lbool &phase){
        if (!m_next_split_expr)
            return false;
        
        euf::enode* n = ctx.get_enode(m_next_split_expr);
        var = n->bool_var();
        phase = m_next_split_phase;
        m_next_split_expr = nullptr;
        return true;
    }

    void solver::asserted(sat::literal lit) {
        if (!m_fixed_eh)
            return;
        force_push();
        auto* n = bool_var2enode(lit.var());
        euf::theory_var v = n->get_th_var(get_id());
        sat::literal_vector lits;
        lits.push_back(lit);
        m_id2justification.setx(v, lits, sat::literal_vector());
        m_fixed_eh(m_user_context, this, var2expr(v), lit.sign() ? m.mk_false() : m.mk_true());
    }
    
    void solver::new_eq_eh(euf::th_eq const& eq) {
        if (!m_eq_eh)
            return;
        force_push();
        m_eq_eh(m_user_context, this, var2expr(eq.v1()), var2expr(eq.v2()));
    }
    
    void solver::new_diseq_eh(euf::th_eq const& de) {
        if (!m_diseq_eh)
            return;
        force_push();
        m_diseq_eh(m_user_context, this, var2expr(de.v1()), var2expr(de.v2()));
    }


    void solver::push_core() {
        th_euf_solver::push_core();
        m_prop_lim.push_back(m_prop.size());
        m_push_eh(m_user_context, this);
    }

    void solver::pop_core(unsigned num_scopes) {
        th_euf_solver::pop_core(num_scopes);
        unsigned old_sz = m_prop_lim.size() - num_scopes;
        m_prop.shrink(m_prop_lim[old_sz]);
        m_prop_lim.shrink(old_sz);
        m_pop_eh(m_user_context, this, num_scopes);
    }

    void solver::propagate_consequence(prop_info const& prop) {
        sat::literal lit = ctx.internalize(prop.m_conseq, false, false);
        if (s().value(lit) != l_true) {
            s().assign(lit, mk_justification(m_qhead));
            ++m_stats.m_num_propagations;
        }
    }

    void solver::propagate_new_fixed(prop_info const& prop) {
        new_fixed_eh(prop.m_var, prop.m_conseq, prop.m_lits.size(), prop.m_lits.data());
    }

    bool solver::unit_propagate() {
        if (m_qhead == m_prop.size())
            return false;
        force_push();
        ctx.push(value_trail<unsigned>(m_qhead));
        unsigned np = m_stats.m_num_propagations;
        for (; m_qhead < m_prop.size() && !s().inconsistent(); ++m_qhead) {
            auto const& prop = m_prop[m_qhead];
            if (prop.m_var == euf::null_theory_var)
                propagate_consequence(prop);
            else
                propagate_new_fixed(prop);
        }       
        return np < m_stats.m_num_propagations;
    }

    void solver::collect_statistics(::statistics& st) const {
        st.update("user-propagations", m_stats.m_num_propagations);
        st.update("user-watched", get_num_vars());
    }

    sat::justification solver::mk_justification(unsigned prop_idx) {
        void* mem = get_region().allocate(justification::get_obj_size());
        sat::constraint_base::initialize(mem, this);
        auto* constraint = new (sat::constraint_base::ptr2mem(mem)) justification(prop_idx);
        return sat::justification::mk_ext_justification(s().scope_lvl(), constraint->to_index());
    }

    void solver::get_antecedents(sat::literal l, sat::ext_justification_idx idx, sat::literal_vector & r, bool probing) {
        auto& j = justification::from_index(idx);
        auto const& prop = m_prop[j.m_propagation_index];
        for (unsigned id : prop.m_ids)
            r.append(m_id2justification[id]);        
        for (auto const& p : prop.m_eqs)
            ctx.add_antecedent(probing, expr2enode(p.first), expr2enode(p.second));
    }

    /*
     * All assumptions and equalities have to be true in the current scope.
     * A caller could mistakingly supply some assumption that isn't set.
     */
    void solver::validate_propagation() {
        auto const& prop = m_prop.back();
        for (unsigned id : prop.m_ids)
            for (auto lit: m_id2justification[id])
                VERIFY(s().value(lit) == l_true);
        for (auto const& p : prop.m_eqs)
            VERIFY(expr2enode(p.first)->get_root() == expr2enode(p.second)->get_root());
    }

    std::ostream& solver::display(std::ostream& out) const {
        for (unsigned i = 0; i < get_num_vars(); ++i)
            out << i << ": " << mk_pp(var2expr(i), m) << "\n";
        return out;
    }

    std::ostream& solver::display_justification(std::ostream& out, sat::ext_justification_idx idx) const {
        auto& j = justification::from_index(idx);
        auto const& prop = m_prop[j.m_propagation_index];
        for (unsigned id : prop.m_ids)
            out << id << ": " << m_id2justification[id];
        for (auto const& p : prop.m_eqs)
            out << "v" << mk_pp(p.first, m) << " == v" << mk_pp(p.second, m) << " ";
        return out;
    }

    std::ostream& solver::display_constraint(std::ostream& out, sat::ext_constraint_idx idx) const {
        return display_justification(out, idx);     
    }

    euf::th_solver* solver::clone(euf::solver& dst_ctx) {
        auto* result = alloc(solver, dst_ctx);
        for (unsigned i = 0; i < get_num_vars(); ++i)
            result->add_expr(ctx.copy(dst_ctx, var2enode(i))->get_expr());
        return result;
    }

    sat::literal solver::internalize(expr* e, bool sign, bool root) {
        if (!visit_rec(m, e, sign, root)) {
            TRACE("array", tout << mk_pp(e, m) << "\n";);
            return sat::null_literal;
        }
        sat::literal lit = ctx.expr2literal(e);
        if (sign)
            lit.neg();
        if (root)
            add_unit(lit);
        return lit;
    }

    void solver::internalize(expr* e) {
        visit_rec(m, e, false, false);
    }

    bool solver::visit(expr* e) {
        if (visited(e))
            return true;
        if (!is_app(e) || to_app(e)->get_family_id() != get_id()) {
            ctx.internalize(e);
            return true;
        }
        m_stack.push_back(sat::eframe(e));
        return false;        
    }
    
    bool solver::visited(expr* e) {
        euf::enode* n = expr2enode(e);
        return n && n->is_attached_to(get_id());        
    }
    
    bool solver::post_visit(expr* e, bool sign, bool root) {
        euf::enode* n = expr2enode(e);
        SASSERT(!n || !n->is_attached_to(get_id()));
        if (!n) 
            n = mk_enode(e, false);        
        add_expr(e);
        if (m_created_eh)
            m_created_eh(m_user_context, this, e);
        return true;
    }



}

