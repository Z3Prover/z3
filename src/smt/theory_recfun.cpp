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
#include "ast/ast_ll_pp.h"
#include "ast/for_each_expr.h"
#include "smt/theory_recfun.h"


#define TRACEFN(x) TRACE("recfun", tout << x << '\n';)

namespace smt {

    theory_recfun::theory_recfun(context& ctx)
        : theory(ctx, ctx.get_manager().mk_family_id("recfun")), 
          m_plugin(*reinterpret_cast<recfun::decl::plugin*>(m.get_plugin(get_family_id()))),
          m_util(m_plugin.u()), 
          m_disabled_guards(m),
          m_enabled_guards(m),
          m_preds(m) {
        }

    theory_recfun::~theory_recfun() {
        reset_eh();
    }

    char const * theory_recfun::get_name() const { return "recfun"; }

    theory* theory_recfun::mk_fresh(context* new_ctx) {
        return alloc(theory_recfun, *new_ctx);
    }

    bool theory_recfun::internalize_atom(app * atom, bool gate_ctx) {
        if (!u().has_defs()) {
            return false;
        }
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
        if (!ctx.relevancy() && u().is_defined(atom)) {
            push_case_expand(atom);
        }
        return true;
    }

    bool theory_recfun::internalize_term(app * term) {
        if (!u().has_defs()) {
            return false;
        }
        for (expr* e : *term) {
            ctx.internalize(e, false);
        }
        if (!ctx.e_internalized(term)) {            
            ctx.mk_enode(term, false, false, true);
        }
        if (!ctx.relevancy() && u().is_defined(term)) {
            push_case_expand(term);
        }
        return true; 
    }


    void theory_recfun::reset_eh() {
        m_stats.reset();
        theory::reset_eh();
        m_disabled_guards.reset();
        m_enabled_guards.reset();
        for (auto & kv : m_guard2pending) 
            dealloc(kv.m_value);
        m_guard2pending.reset();
    }

    /*
     * when `n` becomes relevant, if it's `f(t1...tn)` with `f` defined,
     * then case-expand `n`. If it's a macro we can also immediately
     * body-expand it.
     */
    void theory_recfun::relevant_eh(app * n) {
        SASSERT(ctx.relevancy());
        // TRACEFN("relevant_eh: (defined) " <<  u().is_defined(n) << " " << mk_pp(n, m));        
        if (u().is_defined(n) && u().has_defs()) {
            push_case_expand(n);
        }
    }

    void theory_recfun::push_scope_eh() {
        theory::push_scope_eh();
        m_preds_lim.push_back(m_preds.size());
    }

    void theory_recfun::pop_scope_eh(unsigned num_scopes) {
        theory::pop_scope_eh(num_scopes);
        
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
         
    bool theory_recfun::can_propagate() {
        return m_qhead < m_propagation_queue.size();
    }
    
    void theory_recfun::propagate() {
        if (m_qhead == m_propagation_queue.size())
            return;
        ctx.push_trail(value_trail<unsigned>(m_qhead));
        for (; m_qhead < m_propagation_queue.size() && !ctx.inconsistent(); ++m_qhead) {
            auto& p = *m_propagation_queue[m_qhead];
            if (p.is_guard()) 
                activate_guard(p.guard(), *m_guard2pending[p.guard()]);
            else if (p.is_core()) 
                block_core(p.core());
            else if (p.is_case()) 
                assert_case_axioms(p.case_ex());
            else 
                assert_body_axiom(p.body());
        }
    }

    void theory_recfun::push(propagation_item* p) {
        m_propagation_queue.push_back(p);         
        ctx.push_trail(push_back_vector<scoped_ptr_vector<propagation_item>>(m_propagation_queue));        
    }


    /**
     * make clause `depth_limit => ~guard`
     * the guard appears at a depth below the current cutoff.
     */
    void theory_recfun::disable_guard(expr* guard, expr_ref_vector const& guards) {
        SASSERT(!is_enabled_guard(guard));
        app_ref dlimit = m_util.mk_num_rounds_pred(m_num_rounds);
        expr_ref_vector core(m);
        core.push_back(dlimit);
        core.push_back(guard);
        if (!m_guard2pending.contains(guard)) {
            m_disabled_guards.push_back(guard);
            m_guard2pending.insert(guard, alloc(expr_ref_vector, guards));
        }
        TRACEFN("add core: " << core);
        push_core(core);
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
        expr* e = ctx.bool_var2expr(v);
        if (is_true && u().is_case_pred(e)) {
            TRACEFN("assign_case_pred_true " << mk_pp(e, m));
            // body-expand
            push_body_expand(e);
        }
    }

     // replace `vars` by `args` in `e`
    expr_ref theory_recfun::apply_args(
        unsigned depth,
        recfun::vars const & vars,
        expr_ref_vector const & args,
        expr * e) {
        SASSERT(is_standard_order(vars));
        var_subst subst(m, true);
        expr_ref new_body = subst(e, args);
        ctx.get_rewriter()(new_body); // simplify
        set_depth_rec(depth + 1, new_body);
        return new_body;
    }
        
    literal theory_recfun::mk_literal(expr* e) {
        bool is_not = m.is_not(e, e);
        ctx.internalize(e, false);
        literal lit = ctx.get_literal(e);
        ctx.mark_as_relevant(lit);
        if (is_not)
            lit.neg();
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
        ctx.mark_as_relevant(lit);
        return lit;
    }

    void theory_recfun::block_core(expr_ref_vector const& core) {
        literal_vector clause;
        for (expr* e : core)
            clause.push_back(~mk_literal(e));
        ctx.mk_th_axiom(get_id(), clause);
    }

    /**
     * For functions f(args) that are given as macros f(vs) = rhs
     * 
     * 1. substitute `e.args` for `vs` into the macro rhs
     * 2. add unit clause `f(args) = rhs`
     */
    void theory_recfun::assert_macro_axiom(recfun::case_expansion & e) {
        m_stats.m_macro_expansions++;
        TRACEFN("case expansion " << e);
        SASSERT(e.m_def->is_fun_macro());
        auto & vars = e.m_def->get_vars();
        expr_ref lhs(e.m_lhs, m);
        unsigned depth = get_depth(e.m_lhs);
        expr_ref rhs(apply_args(depth, vars, e.m_args, e.m_def->get_rhs()), m);	
        literal lit = mk_eq_lit(lhs, rhs);
        std::function<literal(void)> fn = [&]() { return lit; };
        scoped_trace_stream _tr(*this, fn);
        ctx.mk_th_axiom(get_id(), 1, &lit);
        TRACEFN("macro expansion yields " << pp_lit(ctx, lit));
	    if (has_quantifiers(rhs))
	        throw default_exception("quantified formulas in recursive functions are not supported");
    }

    /**
     * Add case axioms for every case expansion path.
     *
     * assert `p(args) <=> And(guards)` (with CNF on the fly)
     *
     * also body-expand paths that do not depend on any defined fun
     */
    void theory_recfun::assert_case_axioms(recfun::case_expansion & e) {

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
                recfun::body_expansion be(pred_applied, c, e.m_args);
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

        scoped_trace_stream _tr(*this, preds);
        ctx.mk_th_axiom(get_id(), preds);       
    }

    void theory_recfun::activate_guard(expr* pred_applied, expr_ref_vector const& guards) {
        literal concl = mk_literal(pred_applied);
        literal_vector lguards;
        lguards.push_back(concl);
        for (expr* ga : guards) {
            literal guard = mk_literal(ga);
            lguards.push_back(~guard);
            scoped_trace_stream _tr1(*this, ~concl, guard);
            ctx.mk_th_axiom(get_id(), ~concl, guard);
        }
        scoped_trace_stream _tr2(*this, lguards);
        ctx.mk_th_axiom(get_id(), lguards);        
    }

    /**
     * For a guarded definition guards => f(vars) = rhs
     * and occurrence f(args)
     *
     * substitute `args` for `vars` in guards, and rhs
     * add axiom guards[args/vars] => f(args) = rhs[args/vars]
     *
     */
    void theory_recfun::assert_body_axiom(recfun::body_expansion & e) {
        ++m_stats.m_body_expansions;
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
                TRACEFN("body " << e << "\n" << clause << "\n" << guard);
                return;
            }
            if (clause.back() == false_literal) {
                clause.pop_back();
            }
        }        
        clause.push_back(mk_eq_lit(lhs, rhs));
        TRACEFN(e << "\n" << pp_lits(ctx, clause));
        std::function<literal_vector(void)> fn = [&]() { return clause; };
        scoped_trace_stream _tr(*this, fn);
        ctx.mk_th_axiom(get_id(), clause);
        if (has_quantifiers(rhs))
            throw default_exception("quantified formulas in recursive functions are not supported");
    }
    
    final_check_status theory_recfun::final_check_eh() {
        if (can_propagate()) {
            TRACEFN("final\n");
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
            for (expr* e : m_disabled_guards)
                assumptions.push_back(m.mk_not(e));
        }
    }

    // if `dlimit` or a disabled guard occurs in unsat core, return 'true'
    bool theory_recfun::should_research(expr_ref_vector & unsat_core) {
        bool found = false;
        expr* to_delete = nullptr;
        unsigned n = 0;
        unsigned current_depth = UINT_MAX;
        for (auto * ne : unsat_core) {
            expr* e = nullptr;
            if (m.is_not(ne, e) && is_disabled_guard(e)) {
                found = true;
                unsigned depth = get_depth(e);
                if (depth < current_depth) 
                    n = 0;
                if (depth <= current_depth && (ctx.get_random_value() % (++n)) == 0) {
                    to_delete = e;
                    current_depth = depth;
                }
            }
            else if (u().is_num_rounds(ne)) 
                found = true;
        }
        if (found) {
            m_num_rounds++;
            if (!to_delete && !m_disabled_guards.empty()) 
                to_delete = m_disabled_guards.back();
            if (to_delete) {
                m_disabled_guards.erase(to_delete);
                m_enabled_guards.push_back(to_delete);
                IF_VERBOSE(2, verbose_stream() << "(smt.recfun :enable-guard " << mk_pp(to_delete, m) << ")\n");
            }
            else {
                IF_VERBOSE(2, verbose_stream() << "(smt.recfun :increment-round " << m_num_rounds << ")\n");
            }
            for (expr* g : m_enabled_guards)
                push_guard(g);
        }
        TRACEFN("should research " << found);
        return found;
    }

    void theory_recfun::display(std::ostream & out) const {
        out << "recfun\n";
        out << "disabled guards:\n" << m_disabled_guards << "\n";
        out << "enabled guards:\n" << m_enabled_guards << "\n";
    }

    void theory_recfun::collect_statistics(::statistics & st) const {
        st.update("recfun macro expansion", m_stats.m_macro_expansions);
        st.update("recfun case expansion", m_stats.m_case_expansions);
        st.update("recfun body expansion", m_stats.m_body_expansions);
    }

}
