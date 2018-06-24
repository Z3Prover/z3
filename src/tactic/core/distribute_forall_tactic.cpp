/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    distribute_forall_tactic.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2012-02-18.

--*/
#include "tactic/tactical.h"
#include "ast/rewriter/rewriter_def.h"
#include "ast/rewriter/var_subst.h"

class distribute_forall_tactic : public tactic {

    struct rw_cfg : public default_rewriter_cfg {
        ast_manager & m;

        rw_cfg(ast_manager & _m):m(_m) {}
        bool reduce_quantifier(quantifier * old_q,
                               expr * new_body,
                               expr * const * new_patterns,
                               expr * const * new_no_patterns,
                               expr_ref & result,
                               proof_ref & result_pr) {

            if (!is_forall(old_q)) {
                return false;
            }

            if (m.is_not(new_body) && m.is_or(to_app(new_body)->get_arg(0))) {
                // (forall X (not (or F1 ... Fn)))
                // -->
                // (and (forall X (not F1))
                //      ...
                //      (forall X (not Fn)))
                app * or_e        = to_app(to_app(new_body)->get_arg(0));
                unsigned num_args = or_e->get_num_args();
                expr_ref_buffer new_args(m);
                for (unsigned i = 0; i < num_args; i++) {
                    expr * arg     = or_e->get_arg(i);
                    expr * not_arg = m.mk_not(arg);
                    quantifier_ref tmp_q(m);
                    tmp_q = m.update_quantifier(old_q, not_arg);
                    expr_ref new_q = elim_unused_vars(m, tmp_q, params_ref());
                    new_args.push_back(new_q);
                }
                result = m.mk_and(new_args.size(), new_args.c_ptr());
                return true;
            }

            if (m.is_and(new_body)) {
                // (forall X (and F1 ... Fn))
                // -->
                // (and (forall X F1)
                //      ...
                //      (forall X Fn)
                unsigned num_args = to_app(new_body)->get_num_args();
                expr_ref_buffer new_args(m);
                for (unsigned i = 0; i < num_args; i++) {
                    expr * arg     = to_app(new_body)->get_arg(i);
                    quantifier_ref tmp_q(m);
                    tmp_q = m.update_quantifier(old_q, arg);
                    expr_ref new_q = elim_unused_vars(m, tmp_q, params_ref());
                    new_args.push_back(new_q);
                }
                result = m.mk_and(new_args.size(), new_args.c_ptr());
                return true;
            }

            return false;
        }
    };

    struct rw : public rewriter_tpl<rw_cfg> {
        rw_cfg m_cfg;

        rw(ast_manager & m, bool proofs_enabled):
            rewriter_tpl<rw_cfg>(m, proofs_enabled, m_cfg),
            m_cfg(m) {
        }
    };

    rw * m_rw;

public:
    distribute_forall_tactic():m_rw(nullptr) {}

    tactic * translate(ast_manager & m) override {
        return alloc(distribute_forall_tactic);
    }

    void operator()(goal_ref const & g,
                    goal_ref_buffer & result) override {
        SASSERT(g->is_well_sorted());
        ast_manager & m = g->m();
        bool produce_proofs = g->proofs_enabled();
        rw r(m, produce_proofs);
        m_rw = &r;
        result.reset();
        tactic_report report("distribute-forall", *g);

        expr_ref   new_curr(m);
        proof_ref  new_pr(m);
        unsigned size = g->size();
        for (unsigned idx = 0; idx < size; idx++) {
            if (g->inconsistent())
                break;
            expr * curr = g->form(idx);
            r(curr, new_curr, new_pr);
            if (g->proofs_enabled()) {
                proof * pr = g->pr(idx);
                new_pr     = m.mk_modus_ponens(pr, new_pr);
            }
            g->update(idx, new_curr, new_pr, g->dep(idx));
        }

        g->inc_depth();
        result.push_back(g.get());
        TRACE("distribute-forall", g->display(tout););
        SASSERT(g->is_well_sorted());
        m_rw = nullptr;
    }

    void cleanup() override {}
};

tactic * mk_distribute_forall_tactic(ast_manager & m, params_ref const & p) {
    return alloc(distribute_forall_tactic);
}
