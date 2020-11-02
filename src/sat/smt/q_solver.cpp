/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    a_solver.cpp

Abstract:

    Quantifier solver plugin

Author:

    Nikolaj Bjorner (nbjorner) 2020-09-29

--*/

#include "ast/rewriter/var_subst.h"
#include "sat/smt/q_solver.h"
#include "sat/smt/euf_solver.h"
#include "sat/smt/sat_th.h"
#include "ast/normal_forms/pull_quant.h"
#include "ast/well_sorted.h"

namespace q {

    solver::solver(euf::solver& ctx, family_id fid) :
        th_euf_solver(ctx, ctx.get_manager().get_family_name(fid), fid),
        m_mbqi(ctx,  *this)
    {
    }

    void solver::asserted(sat::literal l) {
        expr* e = bool_var2expr(l.var());
        if (!is_forall(e) && !is_exists(e))
            return;
        if (l.sign() == is_forall(e)) 
            add_clause(~l, skolemize(to_quantifier(e)));
        else {            
            add_clause(~l, specialize(to_quantifier(e)));
            ctx.push_vec(m_universal, l);
        }
        m_stats.m_num_quantifier_asserts++;
    }

    sat::check_result solver::check() {
        if (ctx.get_config().m_mbqi) {
            switch (m_mbqi()) {
            case l_true:  return sat::check_result::CR_DONE;
            case l_false: return sat::check_result::CR_CONTINUE;
            case l_undef: return sat::check_result::CR_GIVEUP;
            }
        }
        return sat::check_result::CR_GIVEUP;
    }

    std::ostream& solver::display(std::ostream& out) const {
        return out;
    }

    void solver::collect_statistics(statistics& st) const {
        st.update("quantifier asserts", m_stats.m_num_quantifier_asserts);
        m_mbqi.collect_statistics(st);
    }

    euf::th_solver* solver::clone(euf::solver& ctx) {
        family_id fid = ctx.get_manager().mk_family_id(symbol("quant"));
        return alloc(solver, ctx, fid);
    }

    bool solver::unit_propagate() {
        return false;
    }

    euf::theory_var solver::mk_var(euf::enode* n) {
        SASSERT(is_forall(n->get_expr()) || is_exists(n->get_expr()));
        auto v = euf::th_euf_solver::mk_var(n);
        ctx.attach_th_var(n, this, v);        
        return v;
    }

    sat::literal solver::instantiate(quantifier* _q, bool negate, std::function<expr* (quantifier*, unsigned)>& mk_var) {
        sat::literal sk;
        expr_ref tmp(m);
        quantifier_ref q(_q, m);
        expr_ref_vector vars(m);
        if (negate) {
            q = m.mk_quantifier(
                is_forall(q) ? quantifier_kind::exists_k : quantifier_kind::forall_k,
                q->get_num_decls(), q->get_decl_sorts(), q->get_decl_names(), m.mk_not(q->get_expr()), 
                q->get_weight(), q->get_qid(), q->get_skid());                
        }
        quantifier* q_flat = flatten(q);
        unsigned sz = q_flat->get_num_decls();
        vars.resize(sz, nullptr);
        for (unsigned i = 0; i < sz; ++i) 
            vars[i] = mk_var(q_flat, i);        
        var_subst subst(m);
        expr_ref body = subst(q_flat->get_expr(), vars);
        rewrite(body);
        return mk_literal(body);
    }

    sat::literal solver::skolemize(quantifier* q) {
        std::function<expr* (quantifier*, unsigned)> mk_var = [&](quantifier* q, unsigned i) {
            return m.mk_fresh_const(q->get_decl_name(i), q->get_decl_sort(i));
        };
        return instantiate(q, is_forall(q), mk_var);
    }

    /*
    * Find initial values to instantiate quantifier with so to make it as hard as possible for solver
    * to find values to free variables. 
    */
    sat::literal solver::specialize(quantifier* q) {
        std::function<expr* (quantifier*, unsigned)> mk_var = [&](quantifier* q, unsigned i) {
            return get_unit(q->get_decl_sort(i));
        };
        return instantiate(q, is_exists(q), mk_var);
    }

    void solver::init_search() {
        m_mbqi.init_search();
    }

    sat::literal solver::internalize(expr* e, bool sign, bool root, bool learned) {
        SASSERT(is_forall(e) || is_exists(e));
        sat::bool_var v = ctx.get_si().add_bool_var(e);
        sat::literal lit = ctx.attach_lit(sat::literal(v, sign), e);
        mk_var(ctx.get_egraph().find(e));
        return lit;
    }

    void solver::finalize_model(model& mdl) {
        m_mbqi.finalize_model(mdl);
    }

    quantifier* solver::flatten(quantifier* q) {
        quantifier* q_flat = nullptr;
        if (!has_quantifiers(q->get_expr())) 
            return q;
        if (m_flat.find(q, q_flat))
            return q_flat;
        proof_ref pr(m);
        expr_ref  new_q(m);
        pull_quant pull(m);
        pull(q, new_q, pr);
        SASSERT(is_well_sorted(m, new_q));
        q_flat = to_quantifier(new_q);
        m.inc_ref(q_flat);
        m.inc_ref(q);
        m_flat.insert(q, q_flat);
        ctx.push(insert_ref2_map<euf::solver, ast_manager, quantifier, quantifier>(m, m_flat, q, q_flat));
        return q_flat;
    }

    void solver::init_units() {
        if (!m_unit_table.empty())
            return;
        for (euf::enode* n : ctx.get_egraph().nodes()) {
            if (!n->interpreted() && !m.is_uninterp(m.get_sort(n->get_expr())))
                continue;
            expr* e = n->get_expr();
            sort* s = m.get_sort(e);
            if (m_unit_table.contains(s))
                continue;
            m_unit_table.insert(s, e);
            ctx.push(insert_map<euf::solver, obj_map<sort, expr*>, sort*>(m_unit_table, s));
        }
    }

    expr* solver::get_unit(sort* s) {
        expr* u = nullptr;
        if (m_unit_table.find(s, u))
            return u;
        init_units();
        if (m_unit_table.find(s, u))
            return u;
        model mdl(m);
        expr* val = mdl.get_some_value(s);
        m.inc_ref(val);
        m.inc_ref(s);
        ctx.push(insert_ref2_map<euf::solver, ast_manager, sort, expr>(m, m_unit_table, s, val));
        return val;
    }
}
