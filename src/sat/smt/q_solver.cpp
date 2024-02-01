/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    q_solver.cpp

Abstract:

    Quantifier solver plugin

Author:

    Nikolaj Bjorner (nbjorner) 2020-09-29

--*/

#include "ast/ast_util.h"
#include "ast/well_sorted.h"
#include "ast/rewriter/var_subst.h"
#include "ast/normal_forms/pull_quant.h"
#include "ast/rewriter/inj_axiom.h"
#include "sat/smt/q_solver.h"
#include "sat/smt/euf_solver.h"
#include "sat/smt/sat_th.h"
#include "qe/lite/qe_lite_tactic.h"
#include <iostream>


namespace q {

    solver::solver(euf::solver& ctx, family_id fid) :
        th_euf_solver(ctx, ctx.get_manager().get_family_name(fid), fid),
        m_mbqi(ctx,  *this),
        m_ematch(ctx, *this),
        m_expanded(ctx.get_manager()),
        m_der(ctx.get_manager())
    {
    }

    void solver::asserted(sat::literal l) {
        expr* e = bool_var2expr(l.var());
        if (!is_forall(e) && !is_exists(e))
            return;
        quantifier* q = to_quantifier(e);

        if (l.sign() == is_forall(e)) {
            sat::literal lit = skolemize(q);
            add_clause(~l, lit);
            return;
        }
        quantifier* q_flat = nullptr;
        if (!m_flat.find(q, q_flat)) {
            if (expand(q)) {
                for (expr* e : m_expanded) {
                    sat::literal lit = ctx.internalize(e, l.sign(), false);
                    add_clause(~l, lit);
                }
                return;
            }
            q_flat = flatten(q);
        }
            
        if (is_ground(q_flat->get_expr())) {
            auto lit = ctx.internalize(q_flat->get_expr(), l.sign(), false);
            add_clause(~l, lit);
        }
        else {
            ctx.push_vec(m_universal, l);
            if (ctx.get_config().m_ematching)
                m_ematch.add(q);
        }
        m_stats.m_num_quantifier_asserts++;
    }

    sat::check_result solver::check() {
        if (ctx.get_config().m_ematching && m_ematch())
            return sat::check_result::CR_CONTINUE;

        if (ctx.get_config().m_mbqi) {
            switch (m_mbqi()) {
            case l_true:  
                return sat::check_result::CR_DONE;
            case l_false: 
                return sat::check_result::CR_CONTINUE;
            case l_undef: 
                break;
            }
        }
        return sat::check_result::CR_GIVEUP;
    }

    std::ostream& solver::display(std::ostream& out) const {
        return m_ematch.display(out);
    }

    std::ostream& solver::display_constraint(std::ostream& out, sat::ext_constraint_idx idx) const {
        return m_ematch.display_constraint(out, idx);
    }    

    void solver::collect_statistics(statistics& st) const {
        st.update("q asserts", m_stats.m_num_quantifier_asserts);
        m_mbqi.collect_statistics(st);
        m_ematch.collect_statistics(st);
    }

    euf::th_solver* solver::clone(euf::solver& ctx) {
        family_id fid = ctx.get_manager().mk_family_id(symbol("quant"));
        return alloc(solver, ctx, fid);
    }

    bool solver::unit_propagate() {
        return m_ematch.unit_propagate();
    }

    euf::theory_var solver::mk_var(euf::enode* n) {
        auto v = euf::th_euf_solver::mk_var(n);
        ctx.attach_th_var(n, this, v);        
        return v;
    }

    sat::literal solver::instantiate(quantifier* _q, bool negate, std::function<expr* (quantifier*, unsigned)>& mk_var) {
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

    sat::literal solver::internalize(expr* e, bool sign, bool root) {
        SASSERT(is_forall(e) || is_exists(e));
        sat::bool_var v = ctx.get_si().add_bool_var(e);
        sat::literal lit = ctx.attach_lit(sat::literal(v, false), e);
        mk_var(ctx.get_egraph().find(e));
        if (sign)
            lit.neg();
        return lit;
    }

    void solver::finalize_model(model& mdl) {
        m_mbqi.finalize_model(mdl);
    }

    quantifier* solver::flatten(quantifier* q) {
        quantifier* q_flat = nullptr;
        if (m_flat.find(q, q_flat))
            return q_flat;

        expr_ref new_q(q, m), r(m);
        proof_ref pr(m);
        if (!has_quantifiers(q->get_expr())) {
            if (!ctx.get_config().m_refine_inj_axiom)
                return q;
            if (!simplify_inj_axiom(m, q, new_q))
                return q;
        }
        else if (is_forall(q)) {
            pull_quant pull(m);
            pull(q, new_q, pr);
            SASSERT(is_well_sorted(m, new_q));
        }
        else {
            new_q = q;
        }
        q_flat = to_quantifier(new_q);
        m.inc_ref(q_flat);
        m.inc_ref(q);
        m_flat.insert(q, q_flat);
        ctx.push(insert_ref2_map<ast_manager, quantifier, quantifier>(m, m_flat, q, q_flat));
        return q_flat;
    }

    void solver::init_units() {
        if (!m_unit_table.empty())
            return;
        for (euf::enode* n : ctx.get_egraph().nodes()) {
            if (!n->interpreted() && !m.is_uninterp(n->get_expr()->get_sort()))
                continue;
            expr* e = n->get_expr();
            sort* s = e->get_sort();
            if (m_unit_table.contains(s))
                continue;
            m_unit_table.insert(s, e);
            ctx.push(insert_map<obj_map<sort, expr*>, sort*>(m_unit_table, s));
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
        ctx.push(insert_ref2_map<ast_manager, sort, expr>(m, m_unit_table, s, val));
        return val;
    }

    /**
     * Expand returns true if it was able to rewrite the formula.
     * If the rewrite results in a quantifier, the rewritten quantifier
     * is stored in m_flat to avoid repeated expansions.
     * 
     */
    bool solver::expand(quantifier* q) {
        expr_ref r(q, m);
        proof_ref pr(m);
        ctx.rewrite(r);
        m_der(r, r, pr);
        if (ctx.get_config().m_qe_lite) {
            qe_lite qe(m, ctx.s().params());
            qe(r);
        }
        m_expanded.reset();
        bool updated = q != r;
        if (updated) {
            ctx.rewrite(r);
            if (!is_quantifier(r)) {
                m_expanded.push_back(r);
                return true;
            }            
            if (is_forall(q)  != is_forall(r)) {
                m_expanded.push_back(r);
                return true;
            }
            if (r == q)
                return false;
            q = to_quantifier(r);
        }
        if (is_forall(q)) 
            flatten_and(q->get_expr(), m_expanded);
        else if (is_exists(q)) 
            flatten_or(q->get_expr(), m_expanded);
        else
            UNREACHABLE();

        if (m_expanded.size() == 1 && is_forall(q)) {
            m_expanded.reset();
            flatten_or(q->get_expr(), m_expanded);
            expr_ref split1(m), split2(m), e1(m), e2(m);
            unsigned idx = 0;
            for (unsigned i = m_expanded.size(); i-- > 0; ) {
                expr* arg = m_expanded.get(i);
                if (split(arg, split1, split2)) {
                    if (e1)
                        return false;
                    e1 = split1;
                    e2 = split2;
                    idx = i;
                }
            }
            if (!e1 && updated) {
                m_expanded.reset();
                m_expanded.push_back(r);
                return true;
            }
            if (!e1)
                return false;

            m_expanded[idx] = e1;
            e1 = mk_or(m_expanded);
            m_expanded[idx] = e2;
            e2 = mk_or(m_expanded);
            m_expanded.reset();
            m_expanded.push_back(e1);
            m_expanded.push_back(e2);
        }
        if (m_expanded.size() > 1) {
            for (unsigned i = m_expanded.size(); i-- > 0; ) {
                expr_ref tmp(m.update_quantifier(q, m_expanded.get(i)), m);
                ctx.rewrite(tmp);
                m_expanded[i] = tmp;
            }
            return true;
        }
        else if (m_expanded.size() == 1 && updated) {
            m_expanded[0] = r;
            flatten(to_quantifier(r));
            return true;
        }
        else {
            return false;
        }
    }

    bool solver::split(expr* arg, expr_ref& e1, expr_ref& e2) {
        expr* x, * y, * z;
        if (m.is_not(arg, x) && m.is_or(x, y, z) && is_literal(y) && is_literal(z)) {
            e1 = mk_not(m, y);
            e2 = mk_not(m, z);
            return true;
        }
        if (m.is_iff(arg, x, y) && is_literal(x) && is_literal(y)) {
            e1 = m.mk_implies(x, y);
            e2 = m.mk_implies(y, x);
            return true;
        }
        if (m.is_and(arg, x, y) && is_literal(x) && is_literal(y)) {
            e1 = x;
            e2 = y;
            return true;
        }
        if (m.is_not(arg, z) && m.is_iff(z, x, y) && is_literal(x) && is_literal(y)) {
            e1 = m.mk_or(x, y);
            e2 = m.mk_or(mk_not(m, x), mk_not(m, y));
            return true;
        }
        return false;
    }

    bool solver::is_literal(expr* arg) {
        m.is_not(arg, arg);
        return !m.is_and(arg) && !m.is_or(arg) && !m.is_iff(arg) && !m.is_implies(arg);
    }

    void solver::get_antecedents(sat::literal l, sat::ext_justification_idx idx, sat::literal_vector& r, bool probing) {
        m_ematch.get_antecedents(l, idx, r, probing);
    }

    void solver::log_instantiation(unsigned n, sat::literal const* lits, justification* j) {
        TRACE("q", for (unsigned i = 0; i < n; ++i) tout << literal2expr(lits[i]) << "\n";);
        if (get_config().m_instantiations2console) {
            ctx.on_instantiation(n, lits, j ? j->m_clause.num_decls() : 0, j ? j->m_binding : nullptr);
        }
    }

    q_proof_hint* q_proof_hint::mk(euf::solver& s, symbol const& method, unsigned generation, sat::literal_vector const& lits, unsigned n, euf::enode* const* bindings) {
        SASSERT(n > 0);
        auto* mem = s.get_region().allocate(q_proof_hint::get_obj_size(n, lits.size()));
        q_proof_hint* ph = new (mem) q_proof_hint(method, generation, n, lits.size());
        for (unsigned i = 0; i < n; ++i)
            ph->m_bindings[i] = bindings[i]->get_expr();
        for (unsigned i = 0; i < lits.size(); ++i)
            ph->m_literals[i] = lits[i];
        return ph;
    }

    q_proof_hint* q_proof_hint::mk(euf::solver& s, symbol const& method, unsigned generation, sat::literal l1, sat::literal l2, unsigned n, expr* const* bindings) {
        SASSERT(n > 0);
        auto* mem = s.get_region().allocate(q_proof_hint::get_obj_size(n, 2));
        q_proof_hint* ph = new (mem) q_proof_hint(method, generation, n, 2);
        for (unsigned i = 0; i < n; ++i)
            ph->m_bindings[i] = bindings[i];
        ph->m_literals[0] = l1;
        ph->m_literals[1] = l2;
        return ph;
    }

    expr* q_proof_hint::get_hint(euf::solver& s) const {
        ast_manager& m = s.get_manager();
        expr_ref_vector args(m);
        expr_ref binding(m);
        arith_util a(m);
        expr_ref gen(a.mk_int(m_generation), m);
        expr* gens[1] = { gen.get() };
        sort* range = m.mk_proof_sort();
        for (unsigned i = 0; i < m_num_bindings; ++i) 
            args.push_back(m_bindings[i]);
        binding = m.mk_app(symbol("bind"), args.size(), args.data(), range);
        args.reset();
        for (unsigned i = 0; i < m_num_literals; ++i) 
            args.push_back(s.literal2expr(~m_literals[i]));
        args.push_back(binding);        
        args.push_back(m.mk_app(symbol("gen"), 1, gens, range));
        args.push_back(m.mk_const(m_method, range));
        return m.mk_app(symbol("inst"), args.size(), args.data(), range);
    }

}
