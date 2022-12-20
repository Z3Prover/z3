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
#include "ast/simplifiers/dependent_expr_state.h"
#include "ast/simplifiers/distribute_forall.h"

struct distribute_forall_simplifier::rw_cfg : public default_rewriter_cfg {
    ast_manager & m;

    rw_cfg(ast_manager & m):m(m) {}

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

            if (!m.is_and(new_body) && !(m.is_not(new_body, f) && (m.is_implies(f) || m.is_or(f))))
                return false;
            flatten_and(new_body, es);
            unsigned i = 0;
            for (expr* arg : es) {
                tmp_q = m.update_quantifier(old_q, arg);
                es[i++] = elim_unused_vars(m, tmp_q, params_ref());
            }
            result = mk_and(es);
            if (m.proofs_enabled()) 
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
};

