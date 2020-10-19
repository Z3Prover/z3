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

    mbqi::mbqi(euf::solver& ctx, solver& s): 
        ctx(ctx), 
        m_qs(s), 
        m(s.get_manager()), 
        m_model_fixer(ctx, m_qs),
        m_fresh_trail(m) 
    {
        add_plugin(alloc(mbp::arith_project_plugin, m));
        add_plugin(alloc(mbp::datatype_project_plugin, m));
        add_plugin(alloc(mbp::array_project_plugin, m));
    }

    void mbqi::restrict_to_universe(expr * sk, ptr_vector<expr> const & universe) {
        SASSERT(!universe.empty());
        expr_ref_vector eqs(m);
        for (expr * e : universe) 
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
        init_solver();
        ::solver::scoped_push _sp(*m_solver);
        quantifier* q_flat = m_qs.flatten(q);
        auto* qb = specialize(q_flat);  
        if (!qb)
            return l_undef;
        m_solver->assert_expr(qb->mbody);
        lbool r = m_solver->check_sat(0, nullptr);
        if (r == l_undef)
            return r;
        if (r == l_false)
            return l_true;
        model_ref mdl0, mdl1;        
        m_solver->get_model(mdl0); 
        expr_ref proj(m);
        auto add_projection = [&](model& mdl, bool inv) {
            proj = solver_project(mdl, *qb);
            if (!proj)
                return;
            if (is_forall(q))
                m_qs.add_clause(~ctx.expr2literal(q), ctx.b_internalize(proj));
            else
                m_qs.add_clause(ctx.expr2literal(q),  ~ctx.b_internalize(proj));
        };
        bool added = false;
#if 0
        m_model_finder.restrict_instantiations(*m_solver, *mdl0, q_flat, vars);
        for (unsigned i = 0; i < m_max_cex && l_true == m_solver->check_sat(0, nullptr); ++i) {
            m_solver->get_model(mdl1);
            add_projection(*mdl1, true);
            if (!proj)
                break;
            added = true;
            m_solver->assert_expr(m.mk_not(proj));
        }
#endif
        if (!added) {
            add_projection(*mdl0, false);
            added = proj;
        }
        return added ? l_false : l_undef;
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
            result->vbody = subst(result->vbody, vars);
        }
        expr_ref& mbody = result->mbody;
        unsigned sz = q->get_num_decls();
        if (!m_model->eval_expr(q->get_expr(), mbody, true))
            return nullptr;

        mbody = subst(mbody, result->vars);        
        if (is_forall(q)) 
            mbody = m.mk_not(mbody);        
        return result;
    }

    /**
    * A most rudimentary projection operator that only tries to find proxy terms from the set of existing terms.
    * Refinements:
    * - grammar based from MBQI paper 
    * - quantifier elimination based on projection operators defined in qe.
    * 
    * - eliminate as-array terms, use lambda
    * - have mode with inv-term from model-finder
    */
    expr_ref mbqi::basic_project(model& mdl, quantifier* q, app_ref_vector& vars) {
        unsigned sz = q->get_num_decls();
        unsigned max_generation = 0;
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
        expr_ref_vector fmls(m);
        app_ref_vector vars(qb.vars);
        fmls.push_back(m.mk_not(qb.vbody));
        mbp::project_plugin proj(m);
        proj.purify(m_model_fixer, mdl, vars, fmls);
        for (unsigned i = 0; i < vars.size(); ++i) {
            app* v = vars.get(i);
            auto* p = get_plugin(v);
            if (p)
                (*p)(*m_model, vars, fmls);
        }
        if (!vars.empty()) {
            expr_safe_replace esubst(m);
            for (app* v : vars) {
                expr_ref val = assign_value(*m_model, v);
                if (!val)
                    return expr_ref(m);
                esubst.insert(v, val);
            }
            esubst(fmls);
        }
        return expr_ref(m.mk_not(mk_and(fmls)), m);
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

}
