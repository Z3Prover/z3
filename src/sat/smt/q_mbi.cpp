/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    q_mbi.cpp

Abstract:

    Model-based quantifier instantiation plugin

Author:

    Nikolaj Bjorner (nbjorner) 2020-09-29

--*/

#include "ast/ast_trail.h"
#include "ast/ast_util.h"
#include "ast/for_each_expr.h"
#include "ast/rewriter/var_subst.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "qe/mbp/mbp_arith.h"
#include "qe/mbp/mbp_arrays.h"
#include "qe/mbp/mbp_datatypes.h"
#include "sat/smt/sat_th.h"
#include "sat/smt/q_mbi.h"
#include "sat/smt/q_solver.h"
#include "sat/smt/euf_solver.h"


namespace q {

    mbqi::mbqi(euf::solver& ctx, solver& s) :
        ctx(ctx),
        m_qs(s),
        m(s.get_manager()),
        m_model_fixer(ctx, m_qs),
        m_fresh_trail(m) {
        auto* ap = alloc(mbp::arith_project_plugin, m);
        ap->set_check_purified(false);
        ap->set_apply_projection(true);
        add_plugin(ap);
        add_plugin(alloc(mbp::datatype_project_plugin, m));
        add_plugin(alloc(mbp::array_project_plugin, m));
    }

    void mbqi::restrict_to_universe(expr* sk, ptr_vector<expr> const& universe) {
        SASSERT(!universe.empty());
        expr_ref_vector eqs(m);
        for (expr* e : universe)
            eqs.push_back(m.mk_eq(sk, e));
        expr_ref fml(m.mk_or(eqs), m);
        m_solver->assert_expr(fml);
    }

    void mbqi::register_value(expr* e) {
        sort* s = m.get_sort(e);
        obj_hashtable<expr>* values = nullptr;
        if (!m_fresh.find(s, values)) {
            values = alloc(obj_hashtable<expr>);
            m_fresh.insert(s, values);
            m_values.push_back(values);
        }
        if (!values->contains(e)) {
            for (expr* b : *values)
                m_qs.add_unit(~m_qs.eq_internalize(e, b));
            values->insert(e);
            m_fresh_trail.push_back(e);
        }
    }

    // sort -> [ value -> expr ]
    // for fixed value return expr
    // new fixed value is distinct from other expr
    expr_ref mbqi::replace_model_value(expr* e) {
        if (m.is_model_value(e)) {
            register_value(e);
            return expr_ref(e, m);
        }
        if (is_app(e) && to_app(e)->get_num_args() > 0) {
            expr_ref_vector args(m);
            for (expr* arg : *to_app(e))
                args.push_back(replace_model_value(arg));
            return expr_ref(m.mk_app(to_app(e)->get_decl(), args), m);
        }
        return expr_ref(e, m);
    }

    expr_ref mbqi::choose_term(euf::enode* r) {
        unsigned sz = r->class_size();
        unsigned start = ctx.s().rand()() % sz;
        unsigned i = 0;
        for (euf::enode* n : euf::enode_class(r))
            if (i++ >= start)
                return expr_ref(n->get_expr(), m);
        return expr_ref(nullptr, m);
    }

    lbool mbqi::check_forall(quantifier* q) {
        quantifier* q_flat = m_qs.flatten(q);
        auto* qb = specialize(q_flat);
        if (!qb)
            return l_undef;
        if (m.is_false(qb->mbody))
            return l_true;
        init_solver();
        ::solver::scoped_push _sp(*m_solver);
        m_solver->assert_expr(qb->mbody);
        lbool r = m_solver->check_sat(0, nullptr);
        if (r == l_undef)
            return r;
        if (r == l_false)
            return l_true;
        model_ref mdl0, mdl1;
        expr_ref proj(m);
        m_solver->get_model(mdl0);
        sat::literal qlit = ctx.expr2literal(q);
        if (is_exists(q))
            qlit.neg();
        unsigned i = 0;
        if (!qb->var_args.empty()) {        
            ::solver::scoped_push _sp(*m_solver);
            add_domain_eqs(*mdl0, *qb);
            for (; i < m_max_cex && l_true == m_solver->check_sat(0, nullptr); ++i) {
                m_solver->get_model(mdl1);
                proj = solver_project(*mdl1, *qb);
                if (!proj)
                    break;
                TRACE("q", tout << "project: " << proj << "\n";);
                m_qs.add_clause(~qlit, ~ctx.mk_literal(proj));
                m_solver->assert_expr(m.mk_not(proj));
            }
        }
        if (i == 0) {
            add_domain_bounds(*mdl0, *qb);
            proj = solver_project(*mdl0, *qb);
            if (!proj)
                return l_undef;
            TRACE("q", tout << "project-base: " << proj << "\n";);
            m_qs.add_clause(~qlit, ~ctx.mk_literal(proj));
        }
        // TODO: add as top-level clause for relevancy        
        return l_false;
    }

    mbqi::q_body* mbqi::specialize(quantifier* q) {
        mbqi::q_body* result = nullptr;
        var_subst subst(m);
        if (!m_q2body.find(q, result)) {
            unsigned sz = q->get_num_decls();
            result = alloc(q_body, m);
            m_q2body.insert(q, result);
            ctx.push(new_obj_trail<euf::solver, q_body>(result));
            ctx.push(insert_obj_map<euf::solver, quantifier, q_body*>(m_q2body, q));
            app_ref_vector& vars = result->vars;
            vars.resize(sz, nullptr);
            for (unsigned i = 0; i < sz; ++i) {
                sort* s = q->get_decl_sort(i);
                vars[i] = m.mk_fresh_const(q->get_decl_name(i), s, false);
                if (m_model->has_uninterpreted_sort(s))
                    restrict_to_universe(vars.get(i), m_model->get_universe(s));
            }
            expr_ref fml = subst(q->get_expr(), vars);
            extract_var_args(q->get_expr(), *result);
            if (is_forall(q))
                fml = m.mk_not(fml);
            flatten_and(fml, result->vbody);
        }
        expr_ref& mbody = result->mbody;
        if (!m_model->eval_expr(q->get_expr(), mbody, true))
            return nullptr;

        mbody = subst(mbody, result->vars);
        if (is_forall(q))
            mbody = mk_not(m, mbody);
        TRACE("q", tout << "specialize " << mbody << "\n";);
        return result;
    }

    /**
    * A most rudimentary projection operator that only tries to find proxy terms from the set of existing terms.
    * Refinements:
    * - grammar based from MBQI paper
    * - quantifier elimination based on projection operators defined in qe.
    *
    * - eliminate as-array terms, use lambda
    */
    expr_ref mbqi::basic_project(model& mdl, quantifier* q, app_ref_vector& vars) {
        unsigned sz = q->get_num_decls();
        expr_ref_vector vals(m);
        vals.resize(sz, nullptr);
        for (unsigned i = 0; i < sz; ++i) {
            app* v = vars.get(i);
            vals[i] = assign_value(mdl, v);
            if (!vals.get(i))
                return expr_ref(m);
        }
        var_subst subst(m);
        return subst(q->get_expr(), vals);
    }

    expr_ref mbqi::solver_project(model& mdl, q_body& qb) {
        for (app* v : qb.vars)
            m_model->register_decl(v->get_decl(), mdl(v));
        expr_ref_vector fmls(qb.vbody);
        app_ref_vector vars(qb.vars);
        fmls.append(qb.domain_eqs);
        TRACE("q",
            tout << "Project\n";
        tout << *m_model << "\n";
        tout << fmls << "\n";
        tout << "model of projection\n" << mdl << "\n";
        tout << "var args: " << qb.var_args.size() << "\n";
        for (expr* f : fmls)
            if (m_model->is_false(f))
                tout << mk_pp(f, m) << " := false\n";
        );
        // 
        // TBD: need to compute projection based on eliminate_nested_vars,
        // but apply it based on original formulas, or add constraints that
        // nested variable occurrences are equal to their subsitutions.
        // The result may not be a proper projection.
        // 
        eliminate_nested_vars(fmls, qb);
        mbp::project_plugin proj(m);
        proj.extract_literals(*m_model, vars, fmls);
        for (unsigned i = 0; i < vars.size(); ++i) {
            app* v = vars.get(i);
            auto* p = get_plugin(v);
            if (p)
                (*p)(*m_model, vars, fmls);
        }
        return mk_and(fmls);
    }

    /**
    * Add disjunctions to m_solver that restrict the possible values of 
    * arguments to uninterpreted functions. The disjunctions added to the solver
    * are specialized with respect to m_model.
    * Add also disjunctions to the quantifier "domain_eqs", to track the constraints
    * added to the solver.
    */
    void mbqi::add_domain_eqs(model& mdl, q_body& qb) {
        qb.domain_eqs.reset();
        var_subst subst(m);
        for (auto p : qb.var_args) {
            expr_ref bounds = m_model_fixer.restrict_arg(p.first, p.second);           
            if (m.is_true(bounds))
                continue;
            expr_ref vbounds = subst(bounds, qb.vars);
            expr_ref mbounds(m);
            if (!m_model->eval_expr(bounds, mbounds, true))
                return;
            mbounds = subst(mbounds, qb.vars);
            m_solver->assert_expr(mbounds);
            qb.domain_eqs.push_back(vbounds);
        }
    }


    /*
    * Add bounds to sub-terms under uninterpreted functions for projection.
    */
    void mbqi::add_domain_bounds(model& mdl, q_body& qb) {
        qb.domain_eqs.reset();
        for (app* v : qb.vars)
            m_model->register_decl(v->get_decl(), mdl(v));
        if (qb.var_args.empty())
            return;
        var_subst subst(m);
        for (auto p : qb.var_args) {
            expr_ref _term = subst(p.first, qb.vars);
            app_ref  term(to_app(_term), m);
            expr_ref value = (*m_model)(term->get_arg(p.second));
            m_model_fixer.invert_arg(term, p.second, value, qb.domain_eqs);
        }
    }

    /*
    * Remove occurrences of free functions that contain variables.
    * Add top-level equalities for those occurrences.
    * 
    * F[g(t)] -> F[s] & g(t) = s
    * 
    * where 
    * - eval(g(t)) = eval(s), 
    * - t contains bound variables, 
    * - s is ground.
    */
    void mbqi::eliminate_nested_vars(expr_ref_vector& fmls, q_body& qb) {
        if (qb.var_args.empty())
            return;
        expr_safe_replace rep(m);
        var_subst subst(m);
        expr_ref_vector eqs(m);
        for (auto p : qb.var_args) {
            expr_ref _term = subst(p.first, qb.vars);
            app_ref  term(to_app(_term), m);
            expr_ref value = (*m_model)(term);
            expr* s = m_model_fixer.invert_app(term, value);
            rep.insert(term, s);
            eqs.push_back(m.mk_eq(term, s));
        }
        rep(fmls);
        fmls.append(eqs);
    }

    /*
    * Add domain restrictions for every non-ground arguments to uninterpreted functions.
    */
    void mbqi::extract_var_args(expr* _t, q_body& qb) {
        expr_ref t(_t, m);
        for (expr* s : subterms(t)) {
            if (is_ground(s))
                continue;
            if (is_uninterp(s) && to_app(s)->get_num_args() > 0) {
                unsigned i = 0;
                for (expr* arg : *to_app(s)) {
                    if (!is_ground(arg) && !is_uninterp(arg))
                        qb.var_args.push_back(std::make_pair(to_app(s), i));
                    ++i;
                }
            }
        }
    }

    expr_ref mbqi::assign_value(model& mdl, app* v) {
        func_decl* f = v->get_decl();
        expr_ref val(mdl.get_some_const_interp(f), m);
        if (!val)
            return expr_ref(m);
        val = mdl.unfold_as_array(val);
        if (!val)
            return expr_ref(m);
        euf::enode* r = nullptr;
        auto const& v2r = ctx.values2root();
        if (v2r.find(val, r))
            val = choose_term(r);
        else
            val = replace_model_value(val);
        return val;
    }

    lbool mbqi::operator()() {
        lbool result = l_true;
        m_model = nullptr;
        for (sat::literal lit : m_qs.m_universal) {
            quantifier* q = to_quantifier(ctx.bool_var2expr(lit.var()));
            if (!ctx.is_relevant(q))
                continue;
            init_model();
            switch (check_forall(q)) {
            case l_false:
                result = l_false;
                break;
            case l_undef:
                if (result == l_true)
                    result = l_undef;
                break;
            default:
                break;
            }
        }
        m_max_cex += ctx.get_config().m_mbqi_max_cexs;
        return result;
    }

    void mbqi::init_model() {
        if (m_model)
            return;
        m_model = alloc(model, m);
        ctx.update_model(m_model);
    }

    void mbqi::init_solver() {
        if (!m_solver)
            m_solver = mk_smt2_solver(m, ctx.s().params());
    }

    void mbqi::init_search() {
        m_max_cex = ctx.get_config().m_mbqi_max_cexs;
    }

    void mbqi::finalize_model(model& mdl) {
        m_model_fixer(mdl);
    }

    mbp::project_plugin* mbqi::get_plugin(app* var) {
        family_id fid = m.get_sort(var)->get_family_id();
        return m_plugins.get(fid, nullptr);
    }

    void mbqi::add_plugin(mbp::project_plugin* p) {
        family_id fid = p->get_family_id();
        m_plugins.reserve(fid + 1);
        SASSERT(!m_plugins.get(fid, nullptr));
        m_plugins.set(fid, p);
    }

    void mbqi::collect_statistics(statistics& st) const {
        if (m_solver)
            m_solver->collect_statistics(st);
    }

}
