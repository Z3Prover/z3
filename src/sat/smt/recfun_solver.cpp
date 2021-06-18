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
        TRACEFN("case expansion " << e);
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
        if (e.m_def->is_fun_macro()) {
            assert_macro_axiom(e);
            return;
        }

        ++m_stats.m_case_expansions;
        TRACEFN("assert_case_axioms " << e
                << " with " << e.m_def->get_cases().size() << " cases");
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
            assert_guard(pred_applied, guards);
        }
        add_clause(preds);
    }
    
    void solver::assert_guard(expr* pred_applied, expr_ref_vector const& guards) {
        sat::literal_vector lguards;
        for (expr* ga : guards) 
            lguards.push_back(mk_literal(ga));
        add_equiv_and(mk_literal(pred_applied), lguards);
    }

    void solver::block_core(expr_ref_vector const& core) {
        sat::literal_vector clause;
        for (expr* e : core)
            clause.push_back(~mk_literal(e));
        add_clause(clause);
    }

    /**
     * make clause `depth_limit => ~guard`
     * the guard appears at a depth below the current cutoff.
     */
    void solver::disable_guard(expr* guard, expr_ref_vector const& guards) {
        SASSERT(!is_enabled_guard(guard));
        app_ref dlimit = m_util.mk_num_rounds_pred(m_num_rounds);
        expr_ref_vector core(m);
        core.push_back(dlimit);
        core.push_back(guard);
        if (!m_guard2pending.contains(guard)) {
            m_disabled_guards.push_back(guard);
            m_guard2pending.insert(guard, alloc(expr_ref_vector, guards));
        }
        TRACEFN("add clause\n" << core);
        push_c(core);
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
        ++m_stats.m_body_expansions;
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

    void solver::collect_statistics(statistics& st) const {
        st.update("recfun macro expansion", m_stats.m_macro_expansions);
        st.update("recfun case expansion", m_stats.m_case_expansions);
        st.update("recfun body expansion", m_stats.m_body_expansions);
    }

    euf::th_solver* solver::clone(euf::solver& ctx) {
        return alloc(solver, ctx);
    }

    bool solver::unit_propagate() {
        force_push();
        if (m_qhead == m_propagation_queue.size())
            return false;
        ctx.push(value_trail<unsigned>(m_qhead));
        for (; m_qhead < m_propagation_queue.size() && !s().inconsistent(); ++m_qhead) {
            auto& p = *m_propagation_queue[m_qhead];
            if (p.is_guard()) 
                assert_guard(p.guard(), *m_guard2pending[p.guard()]);
            else if (p.is_core()) 
                block_core(p.core());
            else if (p.is_case()) 
                assert_case_axioms(p.case_ex());
            else 
                assert_body_axiom(p.body());
        }
        return true;
    }

    void solver::push_prop(propagation_item* p) {
        m_propagation_queue.push_back(p);         
        ctx.push(push_back_vector<scoped_ptr_vector<propagation_item>>(m_propagation_queue));        
    }

    sat::literal solver::internalize(expr* e, bool sign, bool root, bool redundant) {
        force_push();
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
        force_push();
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
            return true;
        }
        m_stack.push_back(sat::eframe(e));
        return false;        
    }

    bool solver::post_visit(expr* e, bool sign, bool root) {
        euf::enode* n = expr2enode(e);
        SASSERT(!n || !n->is_attached_to(get_id()));
        if (!n) 
            n = mk_enode(e, false);
        SASSERT(!n->is_attached_to(get_id()));
        mk_var(n);
        if (u().is_defined(e) && u().has_defs()) 
            push_case_expand(e);
        return true;
    }

    void solver::add_assumptions() {
        if (u().has_defs() || m_disabled_guards.empty()) {
            app_ref dlimit = m_util.mk_num_rounds_pred(m_num_rounds);
            TRACEFN("add_theory_assumption " << dlimit);
            s().assign_scoped(mk_literal(dlimit));
            for (auto g : m_disabled_guards)
                s().assign_scoped(~mk_literal(g));
        }
    }
    
    bool solver::should_research(sat::literal_vector const& core) {
        bool found = false;
        unsigned min_gen = UINT_MAX;
        expr* to_delete = nullptr;
        unsigned n = 0;
        for (sat::literal lit : core) {
            expr* e = ctx.bool_var2expr(lit.var());
            if (lit.sign() && is_disabled_guard(e)) {
                found = true;
                unsigned gen = ctx.get_max_generation(e);
                if (gen < min_gen) 
                    n = 0;

                if (gen <= min_gen && s().rand()() % (++n) == 0) {
                    to_delete = e;
                    min_gen = gen;
                }
            }
            else if (u().is_num_rounds(e)) 
                found = true;
        }
        if (found) {
            ++m_num_rounds;
            if (!to_delete && !m_disabled_guards.empty())
                to_delete = m_disabled_guards.back();
            if (to_delete) {
                m_disabled_guards.erase(to_delete);
                m_enabled_guards.push_back(to_delete);
                push_guard(to_delete);
                IF_VERBOSE(2, verbose_stream() << "(smt.recfun :enable-guard " << mk_pp(to_delete, m) << ")\n");
            }
            else {
                IF_VERBOSE(2, verbose_stream() << "(smt.recfun :increment-round)\n");
            }
            for (expr* g : m_enabled_guards)
                push_guard(g);
        }
        return found;
    }

    bool solver::add_dep(euf::enode* n, top_sort<euf::enode>& dep) {
        if (n->num_args() == 0)
            dep.insert(n, nullptr);
        for (auto* k : euf::enode_args(n))
            dep.add(n, k);
        return true;
    }

    void solver::add_value(euf::enode* n, model& mdl, expr_ref_vector& values) {
        values.set(n->get_root_id(), n->get_root()->get_expr());
    }
    
}
