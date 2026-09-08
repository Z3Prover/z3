/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    distribute_forall.cpp

Author:

    Leonardo de Moura (leonardo) 2012-02-18.
    Nikolaj Bjorner (nbjorner) 2022-11-24

--*/

#include "ast/ast_util.h"
#include "ast/rewriter/rewriter.h"
#include "ast/rewriter/rewriter_def.h"
#include "ast/rewriter/var_subst.h"
#include "ast/normal_forms/pull_quant.h"
#include "ast/simplifiers/dependent_expr_state.h"
#include "ast/simplifiers/distribute_forall.h"

struct distribute_forall_simplifier::rw_cfg : public default_rewriter_cfg {
    ast_manager &   m;
    pull_nested_quant m_pull;

    rw_cfg(ast_manager & m):m(m), m_pull(m) {}

    // Recognize a "guarded conjunction" body: (or L_1 ... L_k (and F_1 ... F_n))
    // i.e. exactly one disjunct (after flattening ors/nots/implies) is itself a
    // conjunction, the rest are plain literals/guards. Rewrite to the equivalent
    // (and (or L_1 ... L_k F_1) ... (or L_1 ... L_k F_n)), so the subsequent
    // and-over-forall distribution (below) can split it into n independent
    // top-level clauses, each retaining only its own guard + F_i, instead of a
    // single clause whose body couples F_1..F_n together (which otherwise forces
    // a single multi-pattern trigger spanning variables from every F_i at once).
    // Bail out (return false) if more than one disjunct is a conjunction, to
    // avoid a combinatorial blow-up from distributing multiple ANDs at once.
    bool distribute_or_over_and(expr * body, expr_ref & result) {
        expr_ref_vector disjuncts(m);
        flatten_or(body, disjuncts);
        if (disjuncts.size() <= 1)
            return false;
        int and_idx = -1;
        for (unsigned i = 0; i < disjuncts.size(); ++i) {
            if (m.is_and(disjuncts.get(i))) {
                if (and_idx != -1)
                    return false; // more than one AND disjunct: skip to avoid blow-up
                and_idx = (int)i;
            }
        }
        if (and_idx < 0)
            return false;
        expr_ref_vector guard_lits(m);
        for (unsigned i = 0; i < disjuncts.size(); ++i)
            if ((int)i != and_idx)
                guard_lits.push_back(disjuncts.get(i));
        app* and_app = to_app(disjuncts.get(and_idx));
        expr_ref_vector new_conjuncts(m);
        for (expr* fi : *and_app) {
            expr_ref_vector or_args(guard_lits);
            or_args.push_back(fi);
            new_conjuncts.push_back(mk_or(or_args));
        }
        result = mk_and(new_conjuncts);
        return true;
    }

    bool reduce_quantifier(quantifier * old_q,
                           expr * new_body,
                           expr * const * new_patterns,
                           expr * const * new_no_patterns,
                           expr_ref & result,
                           proof_ref & result_pr) {

        quantifier_ref tmp_q(m);
        expr_ref_vector es(m);
        expr* f;
        if (is_forall(old_q)) {
            // (forall X (and F1 ... Fn))
            // -->
            // (and (forall X F1)
            //      ...
            //      (forall X Fn)

            expr_ref body(new_body, m);
            bool is_and_body = m.is_and(body) || (m.is_not(body, f) && (m.is_implies(f) || m.is_or(f)));
            bool did_rewrite = false;
            if (!is_and_body && !m.proofs_enabled()) {
                expr_ref rewritten(m);
                if (distribute_or_over_and(body, rewritten)) {
                    body = rewritten;
                    is_and_body = true;
                    did_rewrite = true;
                }
            }
            if (!is_and_body)
                return false;
            flatten_and(body, es);
            unsigned i = 0;
            for (expr* arg : es) {
                tmp_q = m.update_quantifier(old_q, arg);
                expr_ref elim(m);
                elim = elim_unused_vars(m, tmp_q, params_ref());
                if (did_rewrite && is_quantifier(elim) && is_forall(to_quantifier(elim))) {
                    // per-clause miniscoping: the clause's body may still contain a
                    // guard-guarded nested inner forall, e.g. forall X.(guard \/ forall Y.G).
                    // Pull the inner Y prefix into this clause's own outer quantifier,
                    // independently of the other clauses, so the resulting trigger for G
                    // only ranges over X,Y (not vars from unrelated conjuncts).
                    expr_ref pulled(m);
                    proof_ref pulled_pr(m);
                    m_pull(elim, pulled, pulled_pr);
                    elim = pulled;
                }
                es[i++] = elim;
            }
            result = mk_and(es);
            if (m.proofs_enabled() && !did_rewrite)
                result_pr = m.mk_push_quant(old_q, result);
            return true;
        }
        if (is_exists(old_q)) {
            // (exists X (or F1 ... Fn))
            // -->
            // (or (exists X F1)
            //     ...
            //     (exists X Fn)

            if (!m.is_or(new_body) && !m.is_implies(new_body) && !(m.is_not(new_body, f) && m.is_and(f)))
                return false;
            flatten_or(new_body, es);
            unsigned i = 0;
            for (expr* arg : es) {
                tmp_q = m.update_quantifier(old_q, arg);
                es[i++] = elim_unused_vars(m, tmp_q, params_ref());
            }
            result = mk_or(es);
            if (m.proofs_enabled()) 
                result_pr = m.mk_push_quant(old_q, result);
            return true;
        }       
        return false;
    }
};

struct distribute_forall_simplifier::rw : public rewriter_tpl<rw_cfg> {
    rw_cfg m_cfg;
    
    rw(ast_manager & m, bool proofs_enabled):
        rewriter_tpl<rw_cfg>(m, proofs_enabled, m_cfg),
        m_cfg(m) {
    }
};
        
void distribute_forall_simplifier::reduce() {
    if (!m_fmls.has_quantifiers())
        return;
    rw rw(m, m.proofs_enabled());
    expr_ref r(m);
    proof_ref pr(m);
    for (unsigned idx : indices()) {
        auto const& d = m_fmls[idx];
        if (!has_quantifiers(d.fml()))
            continue;
        rw(d.fml(), r, pr);
        if (r != d.fml())
            m_fmls.update(idx, dependent_expr(m, r, mp(d.pr(), pr), d.dep()));
    }
}

