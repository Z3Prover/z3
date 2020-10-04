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
#include "ast/rewriter/var_subst.h"
#include "sat/smt/sat_th.h"
#include "sat/smt/q_mbi.h"
#include "sat/smt/q_solver.h"
#include "sat/smt/euf_solver.h"


namespace q {

    mbqi::mbqi(euf::solver& ctx, solver& s): 
        ctx(ctx), 
        qs(s), 
        m(s.get_manager()), 
        m_model_fixer(ctx, qs),
        m_model_finder(ctx), 
        m_fresh_trail(m) 
    {}

    void mbqi::restrict_to_universe(expr * sk, ptr_vector<expr> const & universe) {
        SASSERT(!universe.empty());
        expr_ref_vector eqs(m);
        for (expr * e : universe) {
            eqs.push_back(m.mk_eq(sk, e));
        }
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
            for (expr* b : *values) {
                expr_ref eq = ctx.mk_eq(e, b);
                qs.add_unit(~qs.b_internalize(eq));
            }
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
            for (expr* arg : *to_app(e)) {
                args.push_back(replace_model_value(arg));
            }
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
        expr_ref_vector vars(m);
        expr_ref body = specialize(q, vars);        
        m_solver->assert_expr(body);
        lbool r = m_solver->check_sat(0, nullptr);
        if (r == l_undef)
            return r;
        if (r == l_false)
            return l_true;
        model_ref mdl0, mdl1;        
        m_solver->get_model(mdl0); 
        expr_ref proj(m);
        auto add_projection = [&](model& mdl, bool inv) {
            proj = project(mdl, q, vars, inv);
            if (!proj)
                return;
            if (is_forall(q))
                qs.add_clause(~ctx.expr2literal(q), ctx.b_internalize(proj));
            else
                qs.add_clause(ctx.expr2literal(q), ~ctx.b_internalize(proj));
        };
        bool added = false;
#if 0
        m_model_finder.restrict_instantiations(*m_solver, *mdl0, q, vars);
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

    expr_ref mbqi::specialize(quantifier* q, expr_ref_vector& vars) {
        expr_ref body(m);
        unsigned sz = q->get_num_decls();
        if (!m_model->eval_expr(q->get_expr(), body, true))
            return expr_ref(m);
        vars.resize(sz, nullptr);
        for (unsigned i = 0; i < sz; ++i) {
            sort* s = q->get_decl_sort(i);
            vars[i] = m.mk_fresh_const(q->get_decl_name(i), s, false);    
            if (m_model->has_uninterpreted_sort(s)) 
                restrict_to_universe(vars.get(i), m_model->get_universe(s));            
        }
        var_subst subst(m);
        body = subst(body, vars);        
        if (is_forall(q)) 
            body = m.mk_not(body);        
        return body;
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
    expr_ref mbqi::project(model& mdl, quantifier* q, expr_ref_vector& vars, bool inv) {
        unsigned sz = q->get_num_decls();
        unsigned max_generation = 0;
        expr_ref_vector vals(m);
        vals.resize(sz, nullptr);
        auto const& v2r = ctx.values2root();
        for (unsigned i = 0; i < sz; ++i) {
            app* v = to_app(vars.get(i));
            func_decl* f = v->get_decl();
            expr_ref val(mdl.get_some_const_interp(f), m);
            if (!val)
                return expr_ref(m);
            val = mdl.unfold_as_array(val);
            if (!val)
                return expr_ref(m);
            if (inv)
                vals[i] = m_model_finder.inv_term(mdl, q, i, val, max_generation);            
            euf::enode* r = nullptr;
            if (!vals.get(i) && v2r.find(val, r))
                vals[i] = choose_term(r);
            if (!vals.get(i))
                vals[i] = replace_model_value(val);
        }
        var_subst subst(m);
        return subst(q->get_expr(), vals);   
    }

    lbool mbqi::operator()() {
        lbool result = l_true;
        m_model = nullptr;
        for (sat::literal lit : qs.m_universal) {
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

}
