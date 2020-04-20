/*++
Copyright (c) 2018 Microsoft Corporation, Simon Cruanes

Module Name:

    theory_recfun.cpp

Abstract:

    Theory responsible for unrolling recursive functions

Author:

    Simon Cruanes December 2017

Revision History:

--*/

#include "util/stats.h"
#include "ast/ast_util.h"
#include "ast/for_each_expr.h"
#include "smt/theory_recfun.h"
#include "smt/params/smt_params_helper.hpp"


#define TRACEFN(x) TRACE("recfun", tout << x << '\n';)

namespace smt {

    theory_recfun::theory_recfun(ast_manager & m)
        : theory(m.mk_family_id("recfun")), 
          m(m),
          m_plugin(*reinterpret_cast<recfun::decl::plugin*>(m.get_plugin(get_family_id()))),
          m_util(m_plugin.u()), 
          m_disabled_guards(m),
          m_enabled_guards(m),
          m_preds(m),
          m_num_rounds(0),
          m_q_case_expand(), 
          m_q_body_expand() {
        }

    theory_recfun::~theory_recfun() {
        reset_eh();
    }

    char const * theory_recfun::get_name() const { return "recfun"; }

    theory* theory_recfun::mk_fresh(context* new_ctx) {
        return alloc(theory_recfun, new_ctx->get_manager());
    }

    void theory_recfun::init(context* ctx) {
        theory::init(ctx);
        m_num_rounds = 0;
    }

    void theory_recfun::init_search_eh() {
    }

    bool theory_recfun::internalize_atom(app * atom, bool gate_ctx) {
        TRACEFN(mk_pp(atom, m));
        if (!u().has_defs()) {
            return false;
        }
        for (expr * arg : *atom) {
            ctx().internalize(arg, false);
        }
        if (!ctx().e_internalized(atom)) {
            ctx().mk_enode(atom, false, true, false);
        }
        if (!ctx().b_internalized(atom)) {
            bool_var v = ctx().mk_bool_var(atom);
            ctx().set_var_theory(v, get_id());
        }
        if (!ctx().relevancy() && u().is_defined(atom)) {
            push_case_expand(alloc(case_expansion, u(), atom));
        }
        return true;
    }

    bool theory_recfun::internalize_term(app * term) {
        if (!u().has_defs()) {
            return false;
        }
        for (expr* e : *term) {
            ctx().internalize(e, false);
        }
        // the internalization of the arguments may have triggered the internalization of term.
        if (!ctx().e_internalized(term)) {            
            ctx().mk_enode(term, false, false, true);
            if (!ctx().relevancy() && u().is_defined(term)) {
                push_case_expand(alloc(case_expansion, u(), term));
            }
        }

        return true; 
    }

    void theory_recfun::reset_queues() {
        for (auto* e : m_q_case_expand) {
            dealloc(e);
        }
        m_q_case_expand.reset();
        for (auto* e : m_q_body_expand) {
            dealloc(e);
        }
        m_q_body_expand.reset();
        m_q_clauses.clear();        
    }

    void theory_recfun::reset_eh() {
        reset_queues();   
        m_stats.reset();
        theory::reset_eh();
        m_disabled_guards.reset();
        m_enabled_guards.reset();
        m_q_guards.reset();
        for (auto & kv : m_guard2pending) {
            dealloc(kv.m_value);
        }
        m_guard2pending.reset();
    }

    /*
     * when `n` becomes relevant, if it's `f(t1...tn)` with `f` defined,
     * then case-expand `n`. If it's a macro we can also immediately
     * body-expand it.
     */
    void theory_recfun::relevant_eh(app * n) {
        SASSERT(ctx().relevancy());
        TRACEFN("relevant_eh: (defined) " <<  u().is_defined(n) << " " << mk_pp(n, m));        
        if (u().is_defined(n) && u().has_defs()) {
            push_case_expand(alloc(case_expansion, u(), n));
        }
    }

    void theory_recfun::push_scope_eh() {
        theory::push_scope_eh();
        m_preds_lim.push_back(m_preds.size());
    }

    void theory_recfun::pop_scope_eh(unsigned num_scopes) {
        theory::pop_scope_eh(num_scopes);
        reset_queues();
        
        // restore depth book-keeping
        unsigned new_lim = m_preds_lim.size()-num_scopes;
#if 0
        // depth tracking of recursive unfolding is 
        // turned off when enabling this code:
        unsigned start = m_preds_lim[new_lim];
        for (unsigned i = start; i < m_preds.size(); ++i) {
            m_pred_depth.remove(m_preds.get(i));
        }
        m_preds.resize(start);
#endif
        m_preds_lim.shrink(new_lim);
    }
    
    void theory_recfun::restart_eh() {
        TRACEFN("restart");
        reset_queues();
        theory::restart_eh();
    }
     
    bool theory_recfun::can_propagate() {
        return 
            !m_q_case_expand.empty() ||
            !m_q_body_expand.empty() ||
            !m_q_clauses.empty() ||
            !m_q_guards.empty();
    }
    
    void theory_recfun::propagate() {

        for (expr* g : m_q_guards) {
            expr* ng = nullptr;
            VERIFY(m.is_not(g, ng));
            activate_guard(ng, *m_guard2pending[g]);
        }
        m_q_guards.reset();

        for (literal_vector & c : m_q_clauses) {
            TRACEFN("add axiom " << pp_lits(ctx(), c));
            ctx().mk_th_axiom(get_id(), c);
        }
        m_q_clauses.clear();
 		
        for (unsigned i = 0; i < m_q_case_expand.size(); ++i) {
            case_expansion* e = m_q_case_expand[i];
            if (e->m_def->is_fun_macro()) {
                // body expand immediately
                assert_macro_axiom(*e);
            }
            else {
                // case expand
                SASSERT(e->m_def->is_fun_defined());
                assert_case_axioms(*e);                
            }
            dealloc(e);
            m_q_case_expand[i] = nullptr;
        }
        m_stats.m_case_expansions += m_q_case_expand.size();
        m_q_case_expand.reset();

        for (unsigned i = 0; i < m_q_body_expand.size(); ++i) {
            assert_body_axiom(*m_q_body_expand[i]);
            dealloc(m_q_body_expand[i]);
            m_q_body_expand[i] = nullptr;
        }
        m_stats.m_body_expansions += m_q_body_expand.size();
        m_q_body_expand.reset();
    }

    /**
     * make clause `depth_limit => ~guard`
     * the guard appears at a depth below the current cutoff.
     */
    void theory_recfun::disable_guard(expr* guard, expr_ref_vector const& guards) {
        expr_ref nguard(m.mk_not(guard), m);
        if (is_disabled_guard(nguard)) 
            return;
        SASSERT(!is_enabled_guard(nguard));
        literal_vector c;
        app_ref dlimit = m_util.mk_num_rounds_pred(m_num_rounds);
        c.push_back(~mk_literal(dlimit));
        c.push_back(~mk_literal(guard)); 
        m_disabled_guards.push_back(nguard);
        SASSERT(!m_guard2pending.contains(nguard));
        m_guard2pending.insert(nguard, alloc(expr_ref_vector, guards));
        TRACEFN("add clause\n" << pp_lits(ctx(), c));
        m_q_clauses.push_back(std::move(c));
    }

    /**
     * retrieve depth associated with predicate or expression.
     */
    unsigned theory_recfun::get_depth(expr* e) {
        SASSERT(u().is_defined(e) || u().is_case_pred(e));
        unsigned d = 0;
        m_pred_depth.find(e, d);
        return d;
    }

    /**
     * Update depth of subterms of e with respect to d.
     */
    void theory_recfun::set_depth_rec(unsigned d, expr* e) {
        struct insert_c {
            theory_recfun& th;
            unsigned m_depth;
            insert_c(theory_recfun& th, unsigned d): th(th), m_depth(d) {}
            void operator()(app* e) { th.set_depth(m_depth, e); }
            void operator()(quantifier*) {}
            void operator()(var*) {}
        };
        insert_c proc(*this, d);
        for_each_expr(proc, e);
    }

    void theory_recfun::set_depth(unsigned depth, expr* e) {        
        if ((u().is_defined(e) || u().is_case_pred(e)) && !m_pred_depth.contains(e)) {
            m_pred_depth.insert(e, depth);
            m_preds.push_back(e);
        }
    }

    /**
     * if `is_true` and `v = C_f_i(t1...tn)`, 
     *    then body-expand i-th case of `f(t1...tn)`
     */
    void theory_recfun::assign_eh(bool_var v, bool is_true) {
        expr* e = ctx().bool_var2expr(v);
        if (is_true && u().is_case_pred(e)) {
            TRACEFN("assign_case_pred_true " << mk_pp(e, m));
            // body-expand
            push_body_expand(alloc(body_expansion, u(), to_app(e)));            
        }
    }

     // replace `vars` by `args` in `e`
    expr_ref theory_recfun::apply_args(
        unsigned depth,
        recfun::vars const & vars,
        ptr_vector<expr> const & args,
        expr * e) {
        SASSERT(is_standard_order(vars));
        var_subst subst(m, true);
        expr_ref new_body(m);
        new_body = subst(e, args.size(), args.c_ptr());
        ctx().get_rewriter()(new_body); // simplify
        set_depth_rec(depth + 1, new_body);
        return new_body;
    }
        
    literal theory_recfun::mk_literal(expr* e) {
        ctx().internalize(e, false);
        literal lit = ctx().get_literal(e);
        ctx().mark_as_relevant(lit);
        return lit;
    }

    literal theory_recfun::mk_eq_lit(expr* l, expr* r) {
        literal lit;
        if (m.is_true(r) || m.is_false(r)) {
            std::swap(l, r);
        }
        if (m.is_true(l)) {
            lit = mk_literal(r);
        }
        else if (m.is_false(l)) {
            lit = ~mk_literal(r);
        }
        else {
            lit = mk_eq(l, r, false);        
        }
        ctx().mark_as_relevant(lit);
        return lit;
    }

    /**
     * For functions f(args) that are given as macros f(vs) = rhs
     * 
     * 1. substitute `e.args` for `vs` into the macro rhs
     * 2. add unit clause `f(args) = rhs`
     */
    void theory_recfun::assert_macro_axiom(case_expansion & e) {
        m_stats.m_macro_expansions++;
        TRACEFN("case expansion " << pp_case_expansion(e, m));
        SASSERT(e.m_def->is_fun_macro());
        auto & vars = e.m_def->get_vars();
        expr_ref lhs(e.m_lhs, m);
        unsigned depth = get_depth(e.m_lhs);
        expr_ref rhs(apply_args(depth, vars, e.m_args, e.m_def->get_rhs()), m);
        literal lit = mk_eq_lit(lhs, rhs);
        std::function<literal(void)> fn = [&]() { return lit; };
        scoped_trace_stream _tr(*this, fn);
        ctx().mk_th_axiom(get_id(), 1, &lit);
        TRACEFN("macro expansion yields " << pp_lit(ctx(), lit));
    }

    /**
     * Add case axioms for every case expansion path.
     *
     * assert `p(args) <=> And(guards)` (with CNF on the fly)
     *
     * also body-expand paths that do not depend on any defined fun
     */
    void theory_recfun::assert_case_axioms(case_expansion & e) {
        TRACEFN("assert_case_axioms "<< pp_case_expansion(e,m)
                << " with " << e.m_def->get_cases().size() << " cases");
        SASSERT(e.m_def->is_fun_defined());
        // add case-axioms for all case-paths
        // assert this was not defined before.
        literal_vector preds;
        auto & vars = e.m_def->get_vars();
            
        for (recfun::case_def const & c : e.m_def->get_cases()) {
            // applied predicate to `args`
            app_ref pred_applied = c.apply_case_predicate(e.m_args);
            SASSERT(u().owns_app(pred_applied));
            literal concl = mk_literal(pred_applied);
            preds.push_back(concl);

            unsigned depth = get_depth(e.m_lhs);
            set_depth(depth, pred_applied);
            expr_ref_vector guards(m);
            for (auto & g : c.get_guards()) {
                guards.push_back(apply_args(depth, vars, e.m_args, g));
            }
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
        // the disjunction of branches is asserted
        // to close the available cases. 
        std::function<literal_vector(void)> fn2 = [&]() { return preds; };
        scoped_trace_stream _tr2(*this, fn2);
        ctx().mk_th_axiom(get_id(), preds);
    }

    void theory_recfun::activate_guard(expr* pred_applied, expr_ref_vector const& guards) {
        literal concl = mk_literal(pred_applied);
        literal_vector lguards;
        lguards.push_back(concl);
        for (expr* ga : guards) {
            literal guard = mk_literal(ga);
            lguards.push_back(~guard);
            literal c[2] = {~concl, guard};
            std::function<literal_vector(void)> fn = [&]() { return literal_vector(2, c); };
            scoped_trace_stream _tr(*this, fn);
            ctx().mk_th_axiom(get_id(), 2, c);
        }
        std::function<literal_vector(void)> fn1 = [&]() { return lguards; };
        scoped_trace_stream _tr1(*this, fn1);
        ctx().mk_th_axiom(get_id(), lguards);        
    }

    /**
     * For a guarded definition guards => f(vars) = rhs
     * and occurrence f(args)
     *
     * substitute `args` for `vars` in guards, and rhs
     * add axiom guards[args/vars] => f(args) = rhs[args/vars]
     *
     */
    void theory_recfun::assert_body_axiom(body_expansion & e) {
        recfun::def & d = *e.m_cdef->get_def();
        auto & vars = d.get_vars();
        auto & args = e.m_args;
        SASSERT(is_standard_order(vars));
        unsigned depth = get_depth(e.m_pred);
        expr_ref lhs(u().mk_fun_defined(d, args), m);
        expr_ref rhs = apply_args(depth, vars, args, e.m_cdef->get_rhs());
        literal_vector clause;
        for (auto & g : e.m_cdef->get_guards()) {
            expr_ref guard = apply_args(depth, vars, args, g);
            clause.push_back(~mk_literal(guard));
            if (clause.back() == true_literal) {
                TRACEFN("body " << pp_body_expansion(e,m) << "\n" << clause << "\n" << guard);
                return;
            }
            if (clause.back() == false_literal) {
                clause.pop_back();
            }
        }        
        clause.push_back(mk_eq_lit(lhs, rhs));
        std::function<literal_vector(void)> fn = [&]() { return clause; };
        scoped_trace_stream _tr(*this, fn);
        ctx().mk_th_axiom(get_id(), clause);
        TRACEFN("body " << pp_body_expansion(e,m));
        TRACEFN(pp_lits(ctx(), clause));
    }
    
    final_check_status theory_recfun::final_check_eh() {
        TRACEFN("final\n");
        if (can_propagate()) {
            propagate();
            return FC_CONTINUE;
        }
        return FC_DONE;
    }

    void theory_recfun::add_theory_assumptions(expr_ref_vector & assumptions) {
        if (u().has_defs() || !m_disabled_guards.empty()) {
            app_ref dlimit = m_util.mk_num_rounds_pred(m_num_rounds);
            TRACEFN("add_theory_assumption " << dlimit);
            assumptions.push_back(dlimit);
            assumptions.append(m_disabled_guards);
        }
    }

    // if `dlimit` or a disabled guard occurs in unsat core, return 'true'
    bool theory_recfun::should_research(expr_ref_vector & unsat_core) {
        bool found = false;
        expr* to_delete = nullptr;
        unsigned n = 0;
        unsigned current_depth = UINT_MAX;
        for (auto & e : unsat_core) {
            if (is_disabled_guard(e)) {
                found = true;
                expr* ne = nullptr;
                VERIFY(m.is_not(e, ne)); 
                unsigned depth = get_depth(ne);
                if (depth < current_depth)
                    n = 0;
                if (depth <= current_depth && (get_context().get_random_value() % (++n)) == 0) {
                    to_delete = e;
                    current_depth = depth;
                }
            }
            else if (u().is_num_rounds(e)) {
                found = true;
            }
        }
        if (found) {
            m_num_rounds++;
            if (to_delete) {
                m_disabled_guards.erase(to_delete);
                m_enabled_guards.push_back(to_delete);
                m_q_guards.push_back(to_delete);
                IF_VERBOSE(1, verbose_stream() << "(smt.recfun :enable-guard " << mk_pp(to_delete, m) << ")\n");
            }
            else {
                IF_VERBOSE(1, verbose_stream() << "(smt.recfun :increment-round)\n");
            }
        }
        return found;
    }

    void theory_recfun::display(std::ostream & out) const {
        out << "recfun\n";
        out << "disabled guards:\n" << m_disabled_guards << "\n";
    }

    void theory_recfun::collect_statistics(::statistics & st) const {
        st.update("recfun macro expansion", m_stats.m_macro_expansions);
        st.update("recfun case expansion", m_stats.m_case_expansions);
        st.update("recfun body expansion", m_stats.m_body_expansions);
    }

    std::ostream& operator<<(std::ostream & out, theory_recfun::pp_case_expansion const & e) {
        return out << "case_exp(" << mk_pp(e.e.m_lhs, e.m) << ")";
    }

    std::ostream& operator<<(std::ostream & out, theory_recfun::pp_body_expansion const & e) {
        out << "body_exp(" << e.e.m_cdef->get_decl()->get_name();
        for (auto* t : e.e.m_args) {
            out << " " << mk_pp(t,e.m);
        }
        return out << ")";
    }
}
