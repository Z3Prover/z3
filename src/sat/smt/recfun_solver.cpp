/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    recfun_solver.cpp

Abstract:

    Recursive function solver plugin

Author:

    Nikolaj Bjorner (nbjorner) 2021-02-09

--*/

#include "ast/rewriter/var_subst.h"
#include "sat/smt/recfun_solver.h"
#include "sat/smt/euf_solver.h"


#define TRACEFN(x) TRACE("recfun", tout << x << '\n';)


namespace recfun {


    solver::solver(euf::solver& ctx):
        th_euf_solver(ctx, symbol("recfun"), ctx.get_manager().mk_family_id("recfun")),
        m_plugin(*reinterpret_cast<recfun::decl::plugin*>(m.get_plugin(ctx.get_manager().mk_family_id("recfun")))),
        m_util(m_plugin.u()), 
        m_disabled_guards(m),
        m_enabled_guards(m),
        m_preds(m) {
    }    

    solver::~solver() {
        reset();
    }

    void solver::reset() {
        m_propagation_queue.reset();
        m_stats.reset();
        m_disabled_guards.reset();
        m_enabled_guards.reset();
        m_propagation_queue.reset();
        for (auto & kv : m_guard2pending) 
            dealloc(kv.m_value);
        m_guard2pending.reset();
    }

    expr_ref solver::apply_args(vars const & vars, expr_ref_vector const & args, expr * e) {
        SASSERT(is_standard_order(vars));
        var_subst subst(m, true);
        expr_ref new_body = subst(e, args);
        ctx.get_rewriter()(new_body);
        return new_body;
    }

    /**
     * For functions f(args) that are given as macros f(vs) = rhs
     * 
     * 1. substitute `e.args` for `vs` into the macro rhs
     * 2. add unit clause `f(args) = rhs`
     */
    void solver::assert_macro_axiom(case_expansion & e) {
        m_stats.m_macro_expansions++;
        SASSERT(e.m_def->is_fun_macro());
        auto & vars = e.m_def->get_vars();
        auto lhs = e.m_lhs;
        auto rhs = apply_args(vars, e.m_args, e.m_def->get_rhs());
        unsigned generation = std::max(ctx.get_max_generation(lhs), ctx.get_max_generation(rhs));
        euf::solver::scoped_generation _sgen(ctx, generation + 1);
        auto eq = eq_internalize(lhs, rhs);
        add_unit(eq);        
    }

    /**
     * Add case axioms for every case expansion path.
     *
     * assert `p(args) <=> And(guards)` (with CNF on the fly)
     *
     * also body-expand paths that do not depend on any defined fun
     */
    void solver::assert_case_axioms(case_expansion & e) {
        SASSERT(e.m_def->is_fun_defined());
        // add case-axioms for all case-paths
        // assert this was not defined before.
        sat::literal_vector preds;
        auto & vars = e.m_def->get_vars();
            
        for (case_def const & c : e.m_def->get_cases()) {
            // applied predicate to `args`
            app_ref pred_applied = c.apply_case_predicate(e.m_args);
            SASSERT(u().owns_app(pred_applied));
            preds.push_back(mk_literal(pred_applied));
            expr_ref_vector guards(m);
            for (auto & g : c.get_guards()) 
                guards.push_back(apply_args(vars, e.m_args, g));
            if (c.is_immediate()) {
                body_expansion be(pred_applied, c, e.m_args);
                assert_body_axiom(be);            
            }
            else if (!is_enabled_guard(pred_applied)) {
                disable_guard(pred_applied, guards);
                continue;
            }
            activate_guard(pred_applied, guards);
        }
        add_clause(preds);
    }
    
    void solver::activate_guard(expr* pred_applied, expr_ref_vector const& guards) {
        sat::literal_vector lguards;
        for (expr* ga : guards) 
            lguards.push_back(mk_literal(ga));
        add_equiv_and(mk_literal(pred_applied), lguards);
    }

    /**
     * make clause `depth_limit => ~guard`
     * the guard appears at a depth below the current cutoff.
     */
    void solver::disable_guard(expr* guard, expr_ref_vector const& guards) {
        expr_ref nguard(m.mk_not(guard), m);
        if (is_disabled_guard(nguard)) 
            return;
        SASSERT(!is_enabled_guard(nguard));
        sat::literal_vector c;
        app_ref dlimit = m_util.mk_num_rounds_pred(m_num_rounds);
        c.push_back(~mk_literal(dlimit));
        c.push_back(~mk_literal(guard)); 
        m_disabled_guards.push_back(nguard);
        SASSERT(!m_guard2pending.contains(nguard));
        m_guard2pending.insert(nguard, alloc(expr_ref_vector, guards));
        TRACEFN("add clause\n" << c);
        m_propagation_queue.push_back(alloc(propagation_item, c));
    }

    /**
     * For a guarded definition guards => f(vars) = rhs
     * and occurrence f(args)
     *
     * substitute `args` for `vars` in guards, and rhs
     * add axiom guards[args/vars] => f(args) = rhs[args/vars]
     *
     */
    void solver::assert_body_axiom(body_expansion & e) {
        recfun::def & d = *e.m_cdef->get_def();
        auto & vars = d.get_vars();
        auto & args = e.m_args;
        SASSERT(is_standard_order(vars));
        sat::literal_vector clause;
        for (auto & g : e.m_cdef->get_guards()) {
            expr_ref guard = apply_args(vars, args, g);
            if (m.is_false(guard))
                return;
            if (m.is_true(guard))
                continue;
            clause.push_back(~mk_literal(guard));
        }        
        expr_ref lhs(u().mk_fun_defined(d, args), m);
        expr_ref rhs = apply_args(vars, args, e.m_cdef->get_rhs());
        clause.push_back(eq_internalize(lhs, rhs));
        add_clause(clause);
    }

    void solver::get_antecedents(sat::literal l, sat::ext_justification_idx idx, sat::literal_vector& r, bool probing) {
        UNREACHABLE();
    }

    void solver::asserted(sat::literal l) {
        expr* e = ctx.bool_var2expr(l.var());
        if (!l.sign() && u().is_case_pred(e)) 
            push_body_expand(e);
    }

    sat::check_result solver::check() {
        return sat::check_result::CR_DONE;
    }

    std::ostream& solver::display(std::ostream& out) const {
        return out << "disabled guards:\n" << m_disabled_guards << "\n";
    }

    std::ostream& solver::display_constraint(std::ostream& out, sat::ext_constraint_idx idx) const {
        UNREACHABLE();
        return out;
    }

    void solver::collect_statistics(statistics& st) const {
        st.update("recfun macro expansion", m_stats.m_macro_expansions);
        st.update("recfun case expansion", m_stats.m_case_expansions);
        st.update("recfun body expansion", m_stats.m_body_expansions);
    }

    euf::th_solver* solver::clone(euf::solver& ctx) {
        return nullptr;
    }

    bool solver::unit_propagate() {
        if (m_qhead == m_propagation_queue.size())
            return false;
        ctx.push(value_trail<unsigned>(m_qhead));
        for (; m_qhead < m_propagation_queue.size() && !s().inconsistent(); ++m_qhead) {
            auto& p = *m_propagation_queue[m_qhead];
            if (p.is_guard()) {
                expr* ng = nullptr;
                VERIFY(m.is_not(p.m_guard, ng));
                activate_guard(ng, *m_guard2pending[p.m_guard]);
            }
            else if (p.is_clause()) {
                add_clause(p.m_clause);
            }
            else if (p.is_case()) {
                recfun::case_expansion& e = *p.m_case;
                if (e.m_def->is_fun_macro()) 
                    assert_macro_axiom(e);
                else 
                    assert_case_axioms(e);                
                ++m_stats.m_case_expansions;
            } 
            else {
                SASSERT(p.is_body());
                assert_body_axiom(*p.m_body);
                ++m_stats.m_body_expansions;
            }                
        }
        return true;
    }

    void solver::push_body_expand(expr* e) {
        auto* b = alloc(body_expansion, u(), to_app(e));
        m_propagation_queue.push_back(alloc(propagation_item, b));
        ctx.push(push_back_vector<scoped_ptr_vector<propagation_item>>(m_propagation_queue));
    }

    void solver::push_case_expand(expr* e) {
        auto* c = alloc(case_expansion, u(), to_app(e));
        m_propagation_queue.push_back(alloc(propagation_item, c));
        ctx.push(push_back_vector<scoped_ptr_vector<propagation_item>>(m_propagation_queue));        
    }

    sat::literal solver::internalize(expr* e, bool sign, bool root, bool redundant) {
        SASSERT(m.is_bool(e));
        if (!visit_rec(m, e, sign, root, redundant)) {
            TRACE("array", tout << mk_pp(e, m) << "\n";);
            return sat::null_literal;
        }
        auto lit = expr2literal(e);
        if (sign)
            lit.neg();
        return lit;
    }

    void solver::internalize(expr* e, bool redundant) {
        visit_rec(m, e, false, false, redundant);
    }

    bool solver::visited(expr* e) {
        euf::enode* n = expr2enode(e);
        return n && n->is_attached_to(get_id());        
    }

    bool solver::visit(expr* e) {
        if (visited(e))
            return true;
        if (!is_app(e) || to_app(e)->get_family_id() != get_id()) {
            ctx.internalize(e, m_is_redundant);
            euf::enode* n = expr2enode(e);
            // TODO ensure_var(n);
            return true;
        }
        m_stack.push_back(sat::eframe(e));
        return false;        
    }

    bool solver::post_visit(expr* e, bool sign, bool root) {
        euf::enode* n = expr2enode(e);
        app* a = to_app(e);        
        SASSERT(!n || !n->is_attached_to(get_id()));
        if (!n) 
            n = mk_enode(e, false);
        SASSERT(!n->is_attached_to(get_id()));
        mk_var(n);
#if 0
        for (auto* arg : euf::enode_args(n))
            ensure_var(arg);  
        switch (a->get_decl_kind()) {
        default:
            UNREACHABLE();
            break;            
        }
#endif
        if (u().is_defined(e) && u().has_defs()) 
            push_case_expand(e);

        return true;
    }



    euf::theory_var solver::mk_var(euf::enode* n) {
        return euf::null_theory_var;
    }

    void solver::init_search() {

    }
    
    void solver::finalize_model(model& mdl) {
        
    }


    
}
