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
        m_model_fixer(ctx, m_qs) {
        auto* ap = alloc(mbp::arith_project_plugin, m);
        ap->set_check_purified(false);
        ap->set_apply_projection(true);
        add_plugin(ap);
        add_plugin(alloc(mbp::datatype_project_plugin, m));
        add_plugin(alloc(mbp::array_project_plugin, m));
    }

    lbool mbqi::operator()() {
        lbool result = l_true;
        m_model = nullptr;
        m_instantiations.reset();
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
        for (auto p : m_instantiations) {
            unsigned generation = std::get<2>(p);
            euf::solver::scoped_generation sg(ctx, generation + 1);
            m_qs.add_clause(~std::get<0>(p), ~ctx.mk_literal(std::get<1>(p)));
        }
        m_instantiations.reset();
        return result;
    }

    /**
     * Restrict solutions to sk to be among a finite set of expressions drawn from
     * 'universe'. Include only expressions that are equal to some term created
     * using at most 'm_generation_bound' quantifier instantiations.
     */
    void mbqi::restrict_to_universe(expr* sk, ptr_vector<expr> const& universe) {
        SASSERT(!universe.empty());
        expr_ref_vector eqs(m);
        euf::enode* n = nullptr;
        unsigned generation_min = UINT_MAX;
        for (expr* e : universe) {
            if (ctx.values2root().find(e, n)) {
                unsigned g = n->class_generation();
                generation_min = std::min(generation_min, g);
                m_generation_max = std::max(m_generation_max, g);
                if (g > m_generation_bound) 
                    continue;
            }
            eqs.push_back(m.mk_eq(sk, e));
        }
        if (eqs.empty()) {
            for (expr* e : universe) 
                if (ctx.values2root().find(e, n) && n->class_generation() <= generation_min)
                    eqs.push_back(m.mk_eq(sk, e));
        }
        m_solver->assert_expr(mk_or(eqs));
    }

    expr_ref mbqi::replace_model_value(expr* e) {
        auto const& v2r = ctx.values2root();
        euf::enode* r = nullptr;
        if (v2r.find(e, r))
            return choose_term(r);        
        if (is_app(e) && to_app(e)->get_num_args() > 0) {
            expr_ref_vector args(m);
            for (expr* arg : *to_app(e))
                args.push_back(replace_model_value(arg));
            return expr_ref(m.mk_app(to_app(e)->get_decl(), args), m);
        }
        if (m.is_model_value(e))
            return expr_ref(m.mk_model_value(0, e->get_sort()), m);
        return expr_ref(e, m);
    }

    expr_ref mbqi::choose_term(euf::enode* r) {
        unsigned gen = r->generation() + 1;
        unsigned count = 0;
        for (euf::enode* n : euf::enode_class(r)) {
            if (n->generation() < gen) {
                count = 0;
                r = n;
            }
            else if (n->generation() == gen) {
                if ((++count) % m_qs.random() == 0)
                    r = n;
            }
            if (count > m_max_choose_candidates)
                break;
        }
        return expr_ref(r->get_expr(), m);
    }

    lbool mbqi::check_forall(quantifier* q) {
        quantifier* q_flat = m_qs.flatten(q);
        init_solver();
        
        auto* qb = specialize(q_flat);
        if (!qb)
            return l_undef;
        if (m.is_false(qb->mbody))
            return l_true;
        if (quick_check(q, q_flat, *qb))
            return l_false;

        m_generation_bound = 0;
        m_generation_max = 0;
        unsigned inc = 1;
        while (true) {
            ::solver::scoped_push _sp(*m_solver);
            add_universe_restriction(q, *qb);
            m_solver->assert_expr(qb->mbody);
            ++m_stats.m_num_checks;
            lbool r = m_solver->check_sat(0, nullptr);
            if (r == l_undef)
                return r;
            if (r == l_true) {
                model_ref mdl;
                expr_ref proj(m);
                m_solver->get_model(mdl);
                if (check_forall_subst(q, *qb, *mdl))
                    return l_false;
                if (check_forall_default(q, *qb, *mdl))
                    return l_false;
            }
            if (m_generation_bound >= m_generation_max)
                return l_true;
            m_generation_bound += inc;
            inc += 1;
        }
        return l_true;
    }

    bool mbqi::check_forall_default(quantifier* q, q_body& qb, model& mdl) {
        expr_ref_vector eqs(m);
        add_domain_bounds(mdl, qb);
        auto proj = solver_project(mdl, qb, eqs, false);
        if (!proj)
            return false;
        add_instantiation(q, proj);
        return true;
    }

    bool mbqi::check_forall_subst(quantifier* q, q_body& qb, model& mdl0) {
        if (qb.var_args.empty())
            return false;
        model_ref mdl1;
        expr_ref_vector eqs(m);
        unsigned i = 0;
        ::solver::scoped_push _sp(*m_solver);
        add_domain_eqs(mdl0, qb);
        for (; i < m_max_cex; ++i) {
            ++m_stats.m_num_checks;
            if (l_true != m_solver->check_sat(0, nullptr))
                break;
            m_solver->get_model(mdl1);
            auto proj = solver_project(*mdl1, qb, eqs, true);
            if (!proj)
                break;
            add_instantiation(q, proj);
            m_solver->assert_expr(m.mk_not(mk_and(eqs)));
        }
        return i > 0;
    }

    void mbqi::add_instantiation(quantifier* q, expr_ref& proj) {
        sat::literal qlit = ctx.expr2literal(q);
        if (is_exists(q))
            qlit.neg();
        ctx.rewrite(proj);
        TRACE("q", tout << "project: " << proj << "\n";);
        ++m_stats.m_num_instantiations;        
        unsigned generation = ctx.get_max_generation(proj);    
        m_instantiations.push_back(instantiation_t(qlit, proj, generation));
    }

    void mbqi::add_universe_restriction(quantifier* q, q_body& qb) {
        unsigned sz = q->get_num_decls();
        for (unsigned i = 0; i < sz; ++i) {
            sort* s = q->get_decl_sort(i);
            if (m_model->has_uninterpreted_sort(s))
                restrict_to_universe(qb.vars.get(i), m_model->get_universe(s));
        }
    }

    mbqi::q_body* mbqi::specialize(quantifier* q) {
        var_subst subst(m);
        q_body* result = q2body(q);
        expr_ref& mbody = result->mbody;
        if (!m_model->eval_expr(q->get_expr(), mbody, true))
            return nullptr;

        mbody = subst(mbody, result->vars);
        if (is_forall(q))
            mbody = mk_not(m, mbody);
        TRACE("q", tout << "specialize " << mbody << "\n";);
        return result;
    }

    mbqi::q_body* mbqi::q2body(quantifier* q) {
        q_body* result = nullptr;
        if (!m_q2body.find(q, result)) {
            unsigned sz = q->get_num_decls();
            var_subst subst(m);
            result = alloc(q_body, m);
            m_q2body.insert(q, result);
            ctx.push(new_obj_trail<q_body>(result));
            ctx.push(insert_obj_map<quantifier, q_body*>(m_q2body, q));
            app_ref_vector& vars = result->vars;
            vars.resize(sz, nullptr);
            for (unsigned i = 0; i < sz; ++i) {
                sort* s = q->get_decl_sort(i);
                vars[i] = m.mk_fresh_const(q->get_decl_name(i), s, false);
            }
            expr_ref fml = subst(q->get_expr(), vars);
            if (is_forall(q))
                fml = m.mk_not(fml);
            flatten_and(fml, result->vbody);
            extract_free_vars(q, *result);
            extract_var_args(q->get_expr(), *result);
        }
        return result;
    }

    expr_ref mbqi::solver_project(model& mdl, q_body& qb, expr_ref_vector& eqs, bool use_inst) {
        eqs.reset();
        model::scoped_model_completion _sc(mdl, true);
        m_model->reset_eval_cache();
        for (app* v : qb.vars)
            m_model->register_decl(v->get_decl(), mdl(v));
        expr_ref_vector fmls(qb.vbody);
        app_ref_vector vars(qb.vars);
        bool fmls_extracted = false;
        TRACE("q",
              tout << "Project\n";
              tout << *m_model << "\n";
              tout << fmls << "\n";
              tout << "model of projection\n" << mdl << "\n";
              tout << "var args: " << qb.var_args.size() << "\n";
              tout << "domain eqs: " << qb.domain_eqs << "\n";
              for (expr* f : fmls)
                  if (m_model->is_false(f))
                      tout << mk_pp(f, m) << " := false\n";
              tout << "vars: " << vars << "\n";);
           
        expr_safe_replace rep(m);
        for (unsigned i = 0; !use_inst && i < vars.size(); ++i) {
            app* v = vars.get(i);
            auto* p = get_plugin(v);
            if (p && !fmls_extracted) {
                fmls.append(qb.domain_eqs);
                eliminate_nested_vars(fmls, qb);
                mbp::project_plugin proj(m);
                proj.extract_literals(*m_model, vars, fmls);
                fmls_extracted = true;
            }
            if (p)
                (*p)(*m_model, vars, fmls);
        }
        for (app* v : vars) {
            expr_ref term(m);
            expr_ref val = (*m_model)(v);
            val = m_model->unfold_as_array(val);
            term = replace_model_value(val);
            rep.insert(v, term);        
            eqs.push_back(m.mk_eq(v, val));
        }
        rep(fmls);
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

        unsigned sz = qb.vars.size();
        for (unsigned idx = 0; idx < sz; ++idx) {
            if (!qb.is_free(idx))
                continue;
            expr* v = qb.vars.get(qb.vars.size() - idx - 1);
            sort* srt = v->get_sort();
            expr_ref_vector veqs(m), meqs(m);
            auto const& nodes = ctx.get_egraph().nodes();
            unsigned sz = nodes.size();
            unsigned bound = m_max_unbounded_equalities;
            expr_mark visited;
            for (unsigned i = 0; i < sz && 0 < bound; ++i) {
                auto* n = nodes[i];
                expr* e = n->get_expr();
                expr* val = ctx.node2value(n);                
                if (val && e->get_sort() == srt && !m.is_value(e) && !visited.is_marked(val)) {
                    visited.mark(val);
                    veqs.push_back(m.mk_eq(v, e));
                    meqs.push_back(m.mk_eq(v, val));
                    --bound;
                }
            }
            if (veqs.empty())
                continue;
            expr_ref meq = mk_or(meqs);
            expr_ref veq = mk_or(veqs);
            m_solver->assert_expr(meq);
            qb.domain_eqs.push_back(veq);
        }
    }

    /*
    * Add bounds to sub-terms under uninterpreted functions for projection.
    */
    void mbqi::add_domain_bounds(model& mdl, q_body& qb) {
        qb.domain_eqs.reset();
        m_model->reset_eval_cache();
        for (app* v : qb.vars)
            m_model->register_decl(v->get_decl(), mdl(v));
        ctx.model_updated(m_model);
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
        expr_mark visited;
        for (auto p : qb.var_args) {
            expr* e = p.first;
            if (visited.is_marked(e))
                continue;
            visited.mark(e);
            expr_ref _term = subst(e, qb.vars);
            app_ref  term(to_app(_term), m);
            expr_ref value = (*m_model)(term);
            expr* s = m_model_fixer.invert_app(term, value);
            rep.insert(term, s);
            expr_ref eq(m.mk_eq(term, s), m);
            if (m_model->is_false(eq)) {
                IF_VERBOSE(0,
                    verbose_stream() << mk_pp(s, m) << " := " << (*m_model)(s) << "\n";
                verbose_stream() << mk_pp(term, m) << " := " << (*m_model)(term) << "\n";
                verbose_stream() << value << " -> " << (*m_model)(ctx.values2root()[value]->get_expr()) << "\n";
                verbose_stream() << (*m_model)(s) << " -> " << (*m_model)(ctx.values2root()[(*m_model)(s)]->get_expr()) << "\n";
                verbose_stream() << *m_model << "\n";);
            }
            eqs.push_back(eq);
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
                    if (!is_ground(arg) && !is_uninterp(arg) && !qb.is_free(arg))
                        qb.var_args.push_back(std::make_pair(to_app(s), i));
                    ++i;
                }
            }
        }
    }

    /*
    * Extract variable positions that are free.
    */
    void mbqi::extract_free_vars(quantifier* q, q_body& qb) {
        expr_ref fml(q->get_expr(), m);
        expr_ref_vector fmls(m);
        if (is_exists(q))
            fml = m.mk_not(fml);
        flatten_or(fml, fmls);
        expr* a = nullptr, *b = nullptr;
        for (expr* f : fmls) {
            if (!m.is_eq(f, a, b))
                continue;
            if (is_var(a) && !is_var(b))
                qb.set_free(to_var(a)->get_idx());
            if (is_var(b) && !is_var(a))
                qb.set_free(to_var(b)->get_idx());
        }
    }

    bool mbqi::quick_check(quantifier* q, quantifier* q_flat, q_body& qb) {
        unsigned_vector offsets;
        if (!first_offset(offsets, qb.vars))
            return false;
        var_subst subst(m);
        expr_ref body(m);
        unsigned max_rounds = m_max_quick_check_rounds;
        unsigned num_bindings = 0;
        expr_ref_vector binding(m);
        
        for (unsigned i = 0; i < max_rounds && num_bindings < m_max_cex; ++i) {
            set_binding(offsets, qb.vars, binding);
            if (m_model->is_true(qb.vbody)) {
                body = subst(q_flat->get_expr(), binding);
                if (is_forall(q))
                    body = ::mk_not(m, body);
                add_instantiation(q, body);
                ++num_bindings;
            }                
            if (!next_offset(offsets, qb.vars))
                break;            
        }
        return num_bindings > 0;
    }

    bool mbqi::next_offset(unsigned_vector& offsets, app_ref_vector const& vars, unsigned index, unsigned start) {
        auto* v = vars[index];
        sort* srt = v->get_sort();
        auto const& nodes = ctx.get_egraph().nodes();
        unsigned sz = nodes.size();
        for (unsigned i = start; i < sz; ++i) {            
            euf::enode* n = nodes[i];
            if (n->generation() > 0)
                return false;
            expr* e = n->get_expr();
            if (e->get_sort() == srt && !m.is_value(e)) {
                offsets[index] = i;
                return true;
            }
        }
        return false;
    }

    void mbqi::set_binding(unsigned_vector const& offsets, app_ref_vector const& vars, expr_ref_vector& binding) {
        binding.reset();
        auto const& nodes = ctx.get_egraph().nodes();
        m_model->reset_eval_cache();
        for (unsigned j = 0; j < offsets.size(); ++j) {
            unsigned offset = offsets[j];
            binding.push_back(nodes[offset]->get_expr());
            m_model->register_decl(vars[j]->get_decl(), (*m_model)(binding.get(j)));
        }
    }

    bool mbqi::first_offset(unsigned_vector& offsets, app_ref_vector const& vars) {
        offsets.reset();
        offsets.resize(vars.size(), 0);
        for (unsigned i = 0; i < vars.size(); ++i) 
            if (!next_offset(offsets, vars, i, 0))
                return false;
        return true;
    }

    bool mbqi::next_offset(unsigned_vector& offsets, app_ref_vector const& vars) {
        for (unsigned i = 0; i < vars.size(); ++i) {
            if (next_offset(offsets, vars, i, offsets[i] + 1))
                return true;
            for (unsigned j = 0; j <= i; ++j)
                if (!next_offset(offsets, vars, j, 0))
                    return false;
        }
        return false;
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
        family_id fid = var->get_sort()->get_family_id();
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
        st.update("q-num-instantiations", m_stats.m_num_instantiations);
        st.update("q-num-checks", m_stats.m_num_checks);
    }

}
