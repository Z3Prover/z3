
#include "util/stats.h"
#include "ast/ast_util.h"
#include "smt/theory_recfun.h"
#include "smt/params/smt_params_helper.hpp"

#define DEBUG(x) TRACE("recfun", tout << x << '\n';)


namespace smt {

    theory_recfun::theory_recfun(ast_manager & m)
        : theory(m.mk_family_id("recfun")), 
          m_plugin(*reinterpret_cast<recfun_decl_plugin*>(m.get_plugin(get_family_id()))),
          m_util(m_plugin.u()), 
          m_trail(*this),
          m_guards(), m_max_depth(0), m_q_case_expand(), m_q_body_expand(), m_q_clauses()
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
        smt_params_helper p(get_context().get_params());
        set_max_depth(p.recfun_max_depth());
    }

    theory* theory_recfun::mk_fresh(context* new_ctx) {
        return alloc(theory_recfun, new_ctx->get_manager());
    }

    bool theory_recfun::internalize_atom(app * atom, bool gate_ctx) {
        context & ctx = get_context();
        if (! ctx.e_internalized(atom)) {
            unsigned num_args = atom->get_num_args();
            for (unsigned i = 0; i < num_args; ++i)
                ctx.internalize(atom->get_arg(i), false);
            ctx.mk_enode(atom, false, true, false);
        }
        if (! ctx.b_internalized(atom)) {
            bool_var v = ctx.mk_bool_var(atom);
            ctx.set_var_theory(v, get_id());
        }
        return true;
    }

    bool theory_recfun::internalize_term(app * term) {
        context & ctx = get_context();
        for (expr* e : *term) ctx.internalize(e, false);
        // the internalization of the arguments may have triggered the internalization of term.
        if (ctx.e_internalized(term))
            return true;
        ctx.mk_enode(term, false, false, true);
        return true; // the theory doesn't actually map terms to variables
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
     * when `n` becomes relevant, if it's `f(t1…tn)` with `f` defined,
     * then case-expand `n`. If it's a macro we can also immediately
     * body-expand it.
     */
    void theory_recfun::relevant_eh(app * n) {
        SASSERT(get_context().relevancy());
        if (u().is_defined(n)) {
            DEBUG("relevant_eh: (defined) " <<  mk_pp(n, m()));
        
            case_expansion e(u(), n);
            push_case_expand(std::move(e));
        }
    }

    void theory_recfun::push_scope_eh() {
        DEBUG("push_scope");
        theory::push_scope_eh();
        m_trail.push_scope();
    }

    void theory_recfun::pop_scope_eh(unsigned num_scopes) {
        DEBUG("pop_scope " << num_scopes);
        m_trail.pop_scope(num_scopes);
        theory::pop_scope_eh(num_scopes);
        reset_queues();
    }
    
    void theory_recfun::restart_eh() {
        DEBUG("restart");
        reset_queues();
        theory::restart_eh();
    }

    bool theory_recfun::can_propagate() {
        return ! (m_q_case_expand.empty() &&
                  m_q_body_expand.empty() &&
                  m_q_clauses.empty());
    }

    void theory_recfun::propagate() {
        context & ctx = get_context();

        for (literal_vector & c : m_q_clauses) {
            DEBUG("add axiom " << pp_lits(ctx, c.size(), c.c_ptr()));
            ctx.mk_th_axiom(get_id(), c.size(), c.c_ptr());
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
        DEBUG("max-depth conflict");
        context & ctx = get_context();
        literal_vector c;
        // make clause `depth_limit => V_{g : guards} ~ g`
        {
            // first literal must be the depth limit one
            app_ref dlimit = m_util.mk_depth_limit_pred(get_max_depth());
            ctx.internalize(dlimit, false);
            c.push_back(~ ctx.get_literal(dlimit));
            SASSERT(ctx.get_assignment(ctx.get_literal(dlimit)) == l_true);
        }
        for (auto& kv : m_guards) {
            expr * g = & kv.get_key();
            c.push_back(~ ctx.get_literal(g));
        }
        DEBUG("max-depth limit: add clause " << pp_lits(ctx, c.size(), c.c_ptr()));
        SASSERT(std::all_of(c.begin(), c.end(), [&](literal & l) { return ctx.get_assignment(l) == l_false; })); // conflict

        m_q_clauses.push_back(std::move(c));
    }

    // if `is_true` and `v = C_f_i(t1…tn)`, then body-expand i-th case of `f(t1…tn)`
    void theory_recfun::assign_eh(bool_var v, bool is_true) {
        expr* e = get_context().bool_var2expr(v);
        if (!is_true) return;
        if (!is_app(e)) return;
        app* a = to_app(e);
        if (u().is_case_pred(a)) {
            DEBUG("assign_case_pred_true "<< mk_pp(e,m()));
            // add to set of local assumptions, for depth-limit purpose
            {
                m_guards.insert(e, empty());
                m().inc_ref(e);
                insert_ref_map<theory_recfun,guard_set,ast_manager,expr*> trail_elt(m(), m_guards, e);
                m_trail.push(trail_elt);
            }
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
        get_context().get_rewriter()(new_body); // simplify
        return new_body;
    }
    
    app_ref theory_recfun::apply_pred(recfun::case_pred const & p,
                                       ptr_vector<expr> const & args){
        app_ref res(u().mk_case_pred(p, args), m());
        return res;
    }
    
    void theory_recfun::assert_macro_axiom(case_expansion & e) {
        DEBUG("assert_macro_axiom " << pp_case_expansion(e,m()));
        SASSERT(e.m_def->is_fun_macro());
        expr_ref lhs(e.m_lhs, m());
        context & ctx = get_context();
        auto & vars = e.m_def->get_vars();
        // substitute `e.args` into the macro RHS
        expr_ref rhs(apply_args(vars, e.m_args, e.m_def->get_macro_rhs()), m());
        DEBUG("macro expansion yields" << mk_pp(rhs,m()));
        // now build the axiom `lhs = rhs`
        ctx.internalize(rhs, false);
        // add unit clause `lhs=rhs`
        literal l(mk_eq(lhs, rhs, true));
        ctx.mark_as_relevant(l);
        literal_vector lits;
        lits.push_back(l);
        DEBUG("assert_macro_axiom: " << pp_lits(ctx, lits.size(), lits.c_ptr()));
        ctx.mk_th_axiom(get_id(), lits.size(), lits.c_ptr());   
    }

    void theory_recfun::assert_case_axioms(case_expansion & e) {
        DEBUG("assert_case_axioms "<< pp_case_expansion(e,m())
              << " with " << e.m_def->get_cases().size() << " cases");
        SASSERT(e.m_def->is_fun_defined());
        context & ctx = get_context();
        // add case-axioms for all case-paths
        auto & vars = e.m_def->get_vars();
        for (recfun::case_def const & c : e.m_def->get_cases()) {
            // applied predicate to `args`
            app_ref pred_applied = apply_pred(c.get_pred(), e.m_args);
            SASSERT(u().owns_app(pred_applied));
            // substitute arguments in `path`
            expr_ref_vector path(m());
            for (auto & g : c.get_guards()) {
                expr_ref g_applied = apply_args(vars, e.m_args, g);
                path.push_back(g_applied);
            }
            // assert `p(args) <=> And(guards)` (with CNF on the fly)
            ctx.internalize(pred_applied, false);
            ctx.mark_as_relevant(ctx.get_bool_var(pred_applied));
            literal concl = ctx.get_literal(pred_applied);
            {
                // assert `guards=>p(args)`
                literal_vector c;
                c.push_back(concl);
                for (expr* g : path) {
                    ctx.internalize(g, false);
                    c.push_back(~ ctx.get_literal(g));
                }

                //TRACE("recfun", tout << "assert_case_axioms " << pp_case_expansion(e)
                //    << " axiom " << mk_pp(*l) <<"\n";);
                DEBUG("assert_case_axiom " << pp_lits(get_context(), path.size()+1, c.c_ptr()));
                get_context().mk_th_axiom(get_id(), path.size()+1, c.c_ptr());
            }
            {
                // assert `p(args) => guards[i]` for each `i`
                for (expr * _g : path) {
                    SASSERT(ctx.b_internalized(_g));
                    literal g = ctx.get_literal(_g);
                    literal c[2] = {~ concl, g};

                    DEBUG("assert_case_axiom " << pp_lits(get_context(), 2, c));
                    get_context().mk_th_axiom(get_id(), 2, c);
                }
            }

            // also body-expand paths that do not depend on any defined fun
            if (c.is_immediate()) {
                body_expansion be(c, e.m_args);
                assert_body_axiom(be);
            }
        }
    }

    void theory_recfun::assert_body_axiom(body_expansion & e) {
        DEBUG("assert_body_axioms "<< pp_body_expansion(e,m()));
        context & ctx = get_context();
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
        expr_ref_vector guards(m());
        for (auto & g : e.m_cdef->get_guards()) {
            expr_ref new_guard = apply_args(vars, args, g);
            guards.push_back(new_guard);
        }        
        // now build the axiom `conds => lhs = rhs`
        ctx.internalize(rhs, false);
        for (auto& g : guards) ctx.internalize(g, false);
        
        // add unit clause `conds => lhs=rhs`
        literal_vector clause;
        for (auto& g : guards) {
            ctx.internalize(g, false);
            literal l = ~ ctx.get_literal(g);
            ctx.mark_as_relevant(l);
            clause.push_back(l);
        }
        literal l(mk_eq(lhs, rhs, true));
        ctx.mark_as_relevant(l);
        clause.push_back(l);
        DEBUG("assert_body_axiom " << pp_lits(ctx, clause.size(), clause.c_ptr()));
        ctx.mk_th_axiom(get_id(), clause.size(), clause.c_ptr());   
    }
    
    final_check_status theory_recfun::final_check_eh() {
        return FC_DONE;
    }

    void theory_recfun::add_theory_assumptions(expr_ref_vector & assumptions) {
        app_ref dlimit = m_util.mk_depth_limit_pred(get_max_depth());
        DEBUG("add_theory_assumption " << mk_pp(dlimit.get(), m()));
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

#ifdef Z3DEBUG
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
#endif
}
