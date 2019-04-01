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
          m_preds(m),
          m_max_depth(0),
          m_q_case_expand(), 
          m_q_body_expand()
        {
        }

    theory_recfun::~theory_recfun() {
        reset_queues();
    }

    char const * theory_recfun::get_name() const { return "recfun"; }

    theory* theory_recfun::mk_fresh(context* new_ctx) {
        return alloc(theory_recfun, new_ctx->get_manager());
    }

    void theory_recfun::init(context* ctx) {
        theory::init(ctx);
        smt_params_helper p(ctx->get_params());
        m_max_depth = p.recfun_depth();
        if (m_max_depth < 2) m_max_depth = 2;
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
    }

    /*
     * when `n` becomes relevant, if it's `f(t1...tn)` with `f` defined,
     * then case-expand `n`. If it's a macro we can also immediately
     * body-expand it.
     */
    void theory_recfun::relevant_eh(app * n) {
        SASSERT(ctx().relevancy());
        if (u().is_defined(n) && u().has_defs()) {
            TRACEFN("relevant_eh: (defined) " <<  mk_pp(n, m));        
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
    void theory_recfun::assert_max_depth_limit(expr* guard) {
        literal_vector c;
        app_ref dlimit = m_util.mk_depth_limit_pred(m_max_depth);
        c.push_back(~mk_literal(dlimit));
        c.push_back(~mk_literal(guard));        
        TRACEFN("max-depth limit: add clause " << pp_lits(ctx(), c));
        m_q_clauses.push_back(std::move(c));
    }

    /**
     * retrieve depth associated with predicate or expression.
     */
    unsigned theory_recfun::get_depth(expr* e) {
        SASSERT(u().is_defined(e) || u().is_case_pred(e));
        unsigned d = 0;
        m_pred_depth.find(e, d);
        TRACEFN("depth " << d << " " << mk_pp(e, m));
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
            TRACEFN("depth " << depth << " : " << mk_pp(e, m));
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
        TRACEFN("case expansion         " << pp_case_expansion(e, m) << "\n");
        SASSERT(e.m_def->is_fun_macro());
        auto & vars = e.m_def->get_vars();
        expr_ref lhs(e.m_lhs, m);
        unsigned depth = get_depth(e.m_lhs);
        expr_ref rhs(apply_args(depth, vars, e.m_args, e.m_def->get_rhs()), m);
        literal lit = mk_eq_lit(lhs, rhs);
        if (m.has_trace_stream()) log_axiom_instantiation(ctx().bool_var2expr(lit.var()));
        ctx().mk_th_axiom(get_id(), 1, &lit);
        if (m.has_trace_stream()) m.trace_stream() << "[end-of-instance]\n";
        TRACEFN("macro expansion yields " << mk_pp(rhs, m) << "\n" <<
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
        literal_vector preds;
        expr_ref_vector pred_exprs(m);
        for (recfun::case_def const & c : e.m_def->get_cases()) {
            // applied predicate to `args`
            app_ref pred_applied = c.apply_case_predicate(e.m_args);

            // cut off cases below max-depth
            unsigned depth = get_depth(e.m_lhs);
            set_depth(depth, pred_applied);
            SASSERT(u().owns_app(pred_applied));
            literal concl = mk_literal(pred_applied);
            preds.push_back(concl);
            pred_exprs.push_back(pred_applied);

            if (c.is_immediate()) {
                body_expansion be(pred_applied, c, e.m_args);
                assert_body_axiom(be);
            }
            else if (depth >= m_max_depth) {
                assert_max_depth_limit(pred_applied);
                continue;
            }

            literal_vector guards;
            expr_ref_vector exprs(m);
            guards.push_back(concl);
            for (auto & g : c.get_guards()) {
                expr_ref ga = apply_args(depth, vars, e.m_args, g);
                literal guard = mk_literal(ga);
                guards.push_back(~guard);
                exprs.push_back(m.mk_not(ga));
                literal c[2] = {~concl, guard};
                if (m.has_trace_stream()) {
                    app_ref body(m);
                    body = m.mk_implies(pred_applied, ga);
                    log_axiom_instantiation(body);
                }
                ctx().mk_th_axiom(get_id(), 2, c);
                if (m.has_trace_stream()) m.trace_stream() << "[end-of-instance]\n";
            }
            if (m.has_trace_stream()) {
                app_ref body(m);
                body = m.mk_implies(m.mk_not(pred_applied), m.mk_or(exprs.size(), exprs.c_ptr()));
                log_axiom_instantiation(body);
            }
            ctx().mk_th_axiom(get_id(), guards);
            if (m.has_trace_stream()) m.trace_stream() << "[end-of-instance]\n";
        }
        // the disjunction of branches is asserted
        // to close the available cases. 
        if (m.has_trace_stream()) {
            app_ref body(m);
            body = m.mk_or(pred_exprs.size(), pred_exprs.c_ptr());
            log_axiom_instantiation(body);
        }
        ctx().mk_th_axiom(get_id(), preds);
        if (m.has_trace_stream()) m.trace_stream() << "[end-of-instance]\n";
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
        expr_ref_vector exprs(m);
        for (auto & g : e.m_cdef->get_guards()) {
            expr_ref guard = apply_args(depth, vars, args, g);
            clause.push_back(~mk_literal(guard));
            exprs.push_back(guard);
            if (clause.back() == true_literal) {
                TRACEFN("body " << pp_body_expansion(e,m) << "\n" << clause << "\n" << guard);
                return;
            }
            if (clause.back() == false_literal) {
                clause.pop_back();
            }
        }        
        clause.push_back(mk_eq_lit(lhs, rhs));
        if (m.has_trace_stream()) {
            app_ref body(m);
            body = m.mk_implies(m.mk_and(exprs.size(), exprs.c_ptr()), m.mk_eq(lhs, rhs));
            log_axiom_instantiation(body);
        }
        ctx().mk_th_axiom(get_id(), clause);
        if (m.has_trace_stream()) m.trace_stream() << "[end-of-instance]\n";
        TRACEFN("body   " << pp_body_expansion(e,m));
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
        if (u().has_defs()) {
            app_ref dlimit = m_util.mk_depth_limit_pred(m_max_depth);
            TRACEFN("add_theory_assumption " << mk_pp(dlimit.get(), m));
            assumptions.push_back(dlimit);
        }
    }

    // if `dlimit` occurs in unsat core, return 'true'
    bool theory_recfun::should_research(expr_ref_vector & unsat_core) {
        for (auto & e : unsat_core) {
            if (u().is_depth_limit(e)) {
                m_max_depth = (3 * m_max_depth) / 2;
                IF_VERBOSE(1, verbose_stream() << "(smt.recfun :increase-depth " << m_max_depth << ")\n");
                return true;
            }
        }
        return false;
    }

    void theory_recfun::display(std::ostream & out) const {
        out << "recfun{}\n";
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
