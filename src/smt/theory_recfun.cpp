/*++
Copyright (c) 2018 Microsoft Corporation, Simon Cuares

Module Name:

    theory_recfun.cpp

Abstract:

    Theory responsible for unrolling recursive functions

Author:

    Simon Cuares December 2017

Revision History:

--*/

#include "util/stats.h"
#include "ast/ast_util.h"
#include "smt/theory_recfun.h"
#include "smt/params/smt_params_helper.hpp"


#define TRACEFN(x) TRACE("recfun", tout << x << '\n';)

namespace smt {

    theory_recfun::theory_recfun(ast_manager & m)
        : theory(m.mk_family_id("recfun")), 
          m(m),
          m_plugin(*reinterpret_cast<recfun_decl_plugin*>(m.get_plugin(get_family_id()))),
          m_util(m_plugin.u()), 
          m_guard_preds(m),
          m_max_depth(0), 
          m_q_case_expand(), 
          m_q_body_expand()
        {
        }

    theory_recfun::~theory_recfun() {
        reset_queues();
    }

    char const * theory_recfun::get_name() const { return "recfun"; }

    void theory_recfun::init_search_eh() {
        // obtain max depth via parameters
        smt_params_helper p(ctx().get_params());
        set_max_depth(p.recfun_max_depth());
    }

    theory* theory_recfun::mk_fresh(context* new_ctx) {
        return alloc(theory_recfun, new_ctx->get_manager());
    }

    bool theory_recfun::internalize_atom(app * atom, bool gate_ctx) {
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
        return true;
    }

    bool theory_recfun::internalize_term(app * term) {
        for (expr* e : *term) {
            ctx().internalize(e, false);
        }
        // the internalization of the arguments may have triggered the internalization of term.
        if (!ctx().e_internalized(term)) {            
            ctx().mk_enode(term, false, false, true);
        }
        return true; 
    }

    void theory_recfun::reset_queues() {
        m_q_case_expand.reset();
        m_q_body_expand.reset();
        m_q_clauses.clear();
    }

    void theory_recfun::reset_eh() {
        reset_queues();   
        m_stats.reset();
        theory::reset_eh();
    }

    /*
     * when `n` becomes relevant, if it's `f(t1...tn)` with `f` defined,
     * then case-expand `n`. If it's a macro we can also immediately
     * body-expand it.
     */
    void theory_recfun::relevant_eh(app * n) {
        SASSERT(ctx().relevancy());
        if (u().is_defined(n)) {
            TRACEFN("relevant_eh: (defined) " <<  mk_pp(n, m));        
            case_expansion e(u(), n);
            push_case_expand(std::move(e));
        }
    }

    void theory_recfun::push_scope_eh() {
        TRACEFN("push_scope");
        theory::push_scope_eh();
        m_guard_preds_lim.push_back(m_guard_preds.size());
    }

    void theory_recfun::pop_scope_eh(unsigned num_scopes) {
        TRACEFN("pop_scope " << num_scopes);
        theory::pop_scope_eh(num_scopes);
        reset_queues();
        
        // restore guards
        unsigned new_lim = m_guard_preds_lim.size()-num_scopes;
        unsigned start = m_guard_preds_lim[new_lim];
        for (unsigned i = start; i < m_guard_preds.size(); ++i) {
            m_guards[m_guard_preds.get(i)->get_decl()].pop_back();
        }
        m_guard_preds.resize(start);
        m_guard_preds_lim.shrink(new_lim);
    }
    
    void theory_recfun::restart_eh() {
        TRACEFN("restart");
        reset_queues();
        theory::restart_eh();
    }
     
    bool theory_recfun::can_propagate() {
        return ! (m_q_case_expand.empty() &&
                  m_q_body_expand.empty() &&
                  m_q_clauses.empty());
    }
    
    void theory_recfun::propagate() {
 
        for (literal_vector & c : m_q_clauses) {
            TRACEFN("add axiom " << pp_lits(ctx(), c));
            ctx().mk_th_axiom(get_id(), c);
        }
        m_q_clauses.clear();

        for (unsigned i = 0; i < m_q_case_expand.size(); ++i) {
            case_expansion & e = m_q_case_expand[i];
            if (e.m_def->is_fun_macro()) {
                // body expand immediately
                assert_macro_axiom(e);
            }
            else {
                // case expand
                SASSERT(e.m_def->is_fun_defined());
                assert_case_axioms(e);                
            }
        }
        m_q_case_expand.clear();

        for (unsigned i = 0; i < m_q_body_expand.size(); ++i) {
            assert_body_axiom(m_q_body_expand[i]);
        }
        m_q_body_expand.clear();
    }

    void theory_recfun::max_depth_limit(ptr_vector<expr> const& guards) {
        TRACEFN("max-depth limit");
        literal_vector c;
        // make clause `depth_limit => V_{g : guards of non-recursive cases} g`

        // first literal must be the depth limit one
        app_ref dlimit = m_util.mk_depth_limit_pred(get_max_depth());
        c.push_back(~mk_literal(dlimit));
        enable_trace("recfun");
        TRACE("recfun", ctx().display(tout << c.back() << " " << dlimit << "\n"););
        SASSERT(ctx().get_assignment(c.back()) == l_false);        

        for (expr * g : guards) {
            c.push_back(mk_literal(g));
        }
        TRACEFN("max-depth limit: add clause " << pp_lits(ctx(), c));
        m_q_clauses.push_back(std::move(c));
    }

    /**
     * if `is_true` and `v = C_f_i(t1...tn)`, 
     *    then body-expand i-th case of `f(t1...tn)`
     */
    void theory_recfun::assign_eh(bool_var v, bool is_true) {
        expr* e = ctx().bool_var2expr(v);
        if (is_true && u().is_case_pred(e)) {
            TRACEFN("assign_case_pred_true " << mk_pp(e, m));
            app* a = to_app(e);            
            // body-expand
            body_expansion b_e(u(), a);
            push_body_expand(std::move(b_e));            
        }
    }

     // replace `vars` by `args` in `e`
    expr_ref theory_recfun::apply_args(recfun::vars const & vars,
                                       ptr_vector<expr> const & args,
                                       expr * e) {
        SASSERT(is_standard_order(vars));
        var_subst subst(m, true);
        expr_ref new_body(m);
        new_body = subst(e, args.size(), args.c_ptr());
        ctx().get_rewriter()(new_body); // simplify
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
		TRACEFN("case expansion         " << pp_case_expansion(e, m) << "\n");
        SASSERT(e.m_def->is_fun_macro());
        auto & vars = e.m_def->get_vars();
        expr_ref lhs(e.m_lhs, m);
        expr_ref rhs(apply_args(vars, e.m_args, e.m_def->get_macro_rhs()), m);
        literal lit = mk_eq_lit(lhs, rhs);
        ctx().mk_th_axiom(get_id(), 1, &lit);
        TRACEFN("macro expansion yields " << mk_pp(rhs,m) << "\n" <<
                "literal                " << pp_lit(ctx(), lit));
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
        auto & vars = e.m_def->get_vars();
        for (recfun::case_def const & c : e.m_def->get_cases()) {
            // applied predicate to `args`
            app_ref pred_applied = c.apply_case_predicate(e.m_args);
            SASSERT(u().owns_app(pred_applied));
            literal concl = mk_literal(pred_applied);

            literal_vector guards;
            guards.push_back(concl);
            for (auto & g : c.get_guards()) {
                expr_ref ga = apply_args(vars, e.m_args, g);
                literal guard = mk_literal(ga);
                guards.push_back(~guard);
                literal c[2] = {~concl, guard};
                ctx().mk_th_axiom(get_id(), 2, c);
            }
            ctx().mk_th_axiom(get_id(), guards);

            if (c.is_immediate()) {
                body_expansion be(c, e.m_args);
                assert_body_axiom(be);

                // add to set of local assumptions, for depth-limit purpose
                func_decl* d = pred_applied->get_decl();
                m_guard_preds.push_back(pred_applied);
                auto& vec = m_guards.insert_if_not_there2(d, ptr_vector<expr>())->get_data().m_value;
                vec.push_back(pred_applied);
                if (vec.size() == get_max_depth()) {
                    max_depth_limit(vec);
                }
            }
        }
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
        expr_ref lhs(u().mk_fun_defined(d, args), m);
        expr_ref rhs = apply_args(vars, args, e.m_cdef->get_rhs());

        literal_vector clause;
        for (auto & g : e.m_cdef->get_guards()) {
            expr_ref guard = apply_args(vars, args, g);
            clause.push_back(~mk_literal(guard));
        }        
        clause.push_back(mk_eq_lit(lhs, rhs));
        ctx().mk_th_axiom(get_id(), clause);
        TRACEFN("body   " << pp_body_expansion(e,m));
        TRACEFN("clause " << pp_lits(ctx(), clause));
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
        if (u().has_def()) {
            app_ref dlimit = m_util.mk_depth_limit_pred(get_max_depth());
            TRACEFN("add_theory_assumption " << mk_pp(dlimit.get(), m));
            assumptions.push_back(dlimit);
        }
    }

    // if `dlimit` occurs in unsat core, return 'true'
    bool theory_recfun::should_research(expr_ref_vector & unsat_core) {
        for (auto & e : unsat_core) {
            if (u().is_depth_limit(e)) {
                unsigned new_depth = (3 * (1 + get_max_depth())) / 2;
                set_max_depth(new_depth);
                return true;
            }
        }
        return false;
    }

    void theory_recfun::display(std::ostream & out) const {
        out << "recfun{}";
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
        out << "body_exp(" << e.e.m_cdef->get_name();
        for (auto* t : e.e.m_args) {
            out << " " << mk_pp(t,e.m);
        }
        return out << ")";
    }
}
