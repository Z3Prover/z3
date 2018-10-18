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
          m_plugin(*reinterpret_cast<recfun_decl_plugin*>(m.get_plugin(get_family_id()))),
          m_util(m_plugin.u()), 
          m_trail(*this),
          m_guards(), 
          m_max_depth(0), 
          m_q_case_expand(), 
          m_q_body_expand(), 
          m_q_clauses()
        {
        }

    theory_recfun::~theory_recfun() {
        reset_queues();
        for (auto & kv : m_guards) {
            m().dec_ref(kv.m_key);
        }
        m_guards.reset();
    }

    char const * theory_recfun::get_name() const { return "recfun"; }

    void theory_recfun::setup_params() {
        // obtain max depth via parameters
        smt_params_helper p(ctx().get_params());
        set_max_depth(p.recfun_max_depth());
    }

    theory* theory_recfun::mk_fresh(context* new_ctx) {
        return alloc(theory_recfun, new_ctx->get_manager());
    }

    bool theory_recfun::internalize_atom(app * atom, bool gate_ctx) {
        context & ctx = get_context();
        for (expr * arg : *atom) {
            ctx.internalize(arg, false);
        }
        if (!ctx.e_internalized(atom)) {
            ctx.mk_enode(atom, false, true, false);
        }
        if (!ctx.b_internalized(atom)) {
            bool_var v = ctx.mk_bool_var(atom);
            ctx.set_var_theory(v, get_id());
        }
        return true;
    }

    bool theory_recfun::internalize_term(app * term) {
        context & ctx = get_context();
        for (expr* e : *term) {
            ctx.internalize(e, false);
        }
        // the internalization of the arguments may have triggered the internalization of term.
        if (!ctx.e_internalized(term)) {            
            ctx.mk_enode(term, false, false, true);
        }
        return true; 
    }

    void theory_recfun::reset_queues() {
        m_q_case_expand.reset();
        m_q_body_expand.reset();
        m_q_clauses.reset();
    }

    void theory_recfun::reset_eh() {
        m_trail.reset();
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
            TRACEFN("relevant_eh: (defined) " <<  mk_pp(n, m()));        
            case_expansion e(u(), n);
            push_case_expand(std::move(e));
        }
    }

    void theory_recfun::push_scope_eh() {
        TRACEFN("push_scope");
        theory::push_scope_eh();
        m_trail.push_scope();
    }

    void theory_recfun::pop_scope_eh(unsigned num_scopes) {
        TRACEFN("pop_scope " << num_scopes);
        m_trail.pop_scope(num_scopes);
        theory::pop_scope_eh(num_scopes);
        reset_queues();
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
            ctx().mk_th_axiom(get_id(), c.size(), c.c_ptr());
        }
        m_q_clauses.clear();

        for (case_expansion & e : m_q_case_expand) {
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

        for (body_expansion & e : m_q_body_expand) {
            assert_body_axiom(e);
        }
        m_q_body_expand.clear();
    }

    void theory_recfun::max_depth_conflict() {
        TRACEFN("max-depth conflict");
        literal_vector c;
        // make clause `depth_limit => V_{g : guards} ~ g`
        {
            // first literal must be the depth limit one
            app_ref dlimit = m_util.mk_depth_limit_pred(get_max_depth());
            c.push_back(~mk_literal(dlimit));
            SASSERT(ctx().get_assignment(c.back()) == l_true);
        }
        for (auto& kv : m_guards) {
            c.push_back(~ mk_literal(kv.m_key));
        }
        TRACEFN("max-depth limit: add clause " << pp_lits(ctx(), c));
        SASSERT(std::all_of(c.begin(), c.end(), [&](literal & l) { return ctx().get_assignment(l) == l_false; })); // conflict

        m_q_clauses.push_back(std::move(c));
    }

    // if `is_true` and `v = C_f_i(t1...tn)`, then body-expand i-th case of `f(t1...tn)`
    void theory_recfun::assign_eh(bool_var v, bool is_true) {
        expr* e = get_context().bool_var2expr(v);
        if (!is_true || !is_app(e)) return;
        app* a = to_app(e);
        if (u().is_case_pred(a)) {
            TRACEFN("assign_case_pred_true "<< mk_pp(e,m()));
            // add to set of local assumptions, for depth-limit purpose
            SASSERT(!m_guards.contains(e));
            m_guards.insert(e, empty());
            m().inc_ref(e);
            insert_ref_map<theory_recfun,guard_set,ast_manager,expr*> trail_elt(m(), m_guards, e);
            m_trail.push(trail_elt);
            
            if (m_guards.size() > get_max_depth()) {
                // too many body-expansions: depth-limit conflict
                max_depth_conflict();
            }
            else {
                // body-expand
                body_expansion b_e(u(), a);
                push_body_expand(std::move(b_e));
            }
        }
    }

     // replace `vars` by `args` in `e`
    expr_ref theory_recfun::apply_args(recfun::vars const & vars,
                                       ptr_vector<expr> const & args,
                                       expr * e) {
        // check that var order is standard
        SASSERT(vars.size() == 0 || vars[vars.size()-1]->get_idx() == 0);
        var_subst subst(m(), true);
        expr_ref new_body(m());
        new_body = subst(e, args.size(), args.c_ptr());
        ctx().get_rewriter()(new_body); // simplify
        return new_body;
    }
    
    app_ref theory_recfun::apply_pred(recfun::case_pred const & p,
                                       ptr_vector<expr> const & args) {
        return app_ref(u().mk_case_pred(p, args), m());
    }
    
    literal theory_recfun::mk_literal(expr* e) {
        ctx().internalize(e, false);
        literal lit = ctx().get_literal(e);
        ctx().mark_as_relevant(lit);
        return lit;
    }

    literal theory_recfun::mk_eq_lit(expr* l, expr* r) {
        literal lit = mk_eq(l, r, false);
        ctx().mark_as_relevant(lit);
        return lit;
    }

    void theory_recfun::assert_macro_axiom(case_expansion & e) {
        TRACEFN("assert_macro_axiom " << pp_case_expansion(e, m()));
        SASSERT(e.m_def->is_fun_macro());
        auto & vars = e.m_def->get_vars();
        expr_ref lhs(e.m_lhs, m());
        // substitute `e.args` into the macro RHS
        expr_ref rhs(apply_args(vars, e.m_args, e.m_def->get_macro_rhs()), m());
        TRACEFN("macro expansion yields" << mk_pp(rhs,m()));
        // add unit clause `lhs = rhs`
        literal lit = mk_eq_lit(lhs, rhs);
        TRACEFN("assert_macro_axiom: " << pp_lit(ctx(), lit));
        ctx().mk_th_axiom(get_id(), 1, &lit);
    }

    void theory_recfun::assert_case_axioms(case_expansion & e) {
        TRACEFN("assert_case_axioms "<< pp_case_expansion(e,m())
              << " with " << e.m_def->get_cases().size() << " cases");
        SASSERT(e.m_def->is_fun_defined());
        // add case-axioms for all case-paths
        auto & vars = e.m_def->get_vars();
        for (recfun::case_def const & c : e.m_def->get_cases()) {
            // applied predicate to `args`
            literal_vector guards;
            for (auto & g : c.get_guards()) {
                expr_ref guard = apply_args(vars, e.m_args, g);
                guards.push_back(~mk_literal(guard));
            }
            app_ref pred_applied = apply_pred(c.get_pred(), e.m_args);
            SASSERT(u().owns_app(pred_applied));
            literal concl = mk_literal(pred_applied);

            // assert `p(args) <=> And(guards)` (with CNF on the fly)

            for (literal g : guards) {
                literal c[2] = {~ concl, ~g};
                ctx().mk_th_axiom(get_id(), 2, c);
            }
            guards.push_back(concl);
            ctx().mk_th_axiom(get_id(), guards.size(), guards.c_ptr());

            // also body-expand paths that do not depend on any defined fun
            if (c.is_immediate()) {
                body_expansion be(c, e.m_args);
                assert_body_axiom(be);
            }
        }
    }

    void theory_recfun::assert_body_axiom(body_expansion & e) {
        TRACEFN("assert_body_axioms "<< pp_body_expansion(e,m()));
        recfun::def & d = *e.m_cdef->get_def();
        auto & vars = d.get_vars();
        auto & args = e.m_args;
        // check that var order is standard
        SASSERT(vars.size() == 0 || vars[vars.size()-1]->get_idx() == 0);
        expr_ref lhs(u().mk_fun_defined(d, args), m());
        // substitute `e.args` into the RHS of this particular case
        expr_ref rhs = apply_args(vars, args, e.m_cdef->get_rhs());
        // substitute `e.args` into the guard of this particular case, to make
        // the `condition` part of the clause `conds => lhs=rhs`

        // now build the axiom `conds => lhs = rhs`        

        literal_vector clause;
        for (auto & g : e.m_cdef->get_guards()) {
            expr_ref guard = apply_args(vars, args, g);
            clause.push_back(~mk_literal(guard));
        }        
        clause.push_back(mk_eq_lit(lhs, rhs));
        TRACEFN("assert_body_axiom " << pp_lits(ctx(), clause));
        ctx().mk_th_axiom(get_id(), clause.size(), clause.c_ptr());   
    }
    
    final_check_status theory_recfun::final_check_eh() {
        return FC_DONE;
    }

    void theory_recfun::add_theory_assumptions(expr_ref_vector & assumptions) {
        app_ref dlimit = m_util.mk_depth_limit_pred(get_max_depth());
        TRACEFN("add_theory_assumption " << mk_pp(dlimit.get(), m()));
        assumptions.push_back(dlimit);
    }


    // if `dlimit` occurs in unsat core, return "unknown"
    lbool theory_recfun::validate_unsat_core(expr_ref_vector & unsat_core) {
        for (auto & e : unsat_core) {
            if (is_app(e) && m_util.is_depth_limit(to_app(e)))
                return l_undef;
        }
        return l_false;
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
