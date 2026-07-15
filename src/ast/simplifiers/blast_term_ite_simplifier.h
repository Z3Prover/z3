/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    blast_term_ite_simplifier.h

Author:

    Nikolaj Bjorner (nbjorner) 2013-11-4

--*/

#pragma once

#include "ast/simplifiers/dependent_expr_state.h"
#include "ast/rewriter/rewriter_def.h"
#include "ast/scoped_proof.h"
#include "params/tactic_params.hpp"


class blast_term_ite_simplifier : public dependent_expr_simplifier {

    struct rw_cfg : public default_rewriter_cfg {
        ast_manager&         m;
        unsigned             m_num_fresh;
        unsigned             m_max_steps;
        unsigned             m_max_inflation;
        unsigned             m_init_term_size;

        rw_cfg(ast_manager& _m, params_ref const& p):
            m(_m),
            m_num_fresh(0),
            m_max_steps(UINT_MAX),
            m_max_inflation(UINT_MAX),
            m_init_term_size(0) {
            updt_params(p);
        }

        void updt_params(params_ref const& p) {
            tactic_params tp(p);
            m_max_steps     = p.get_uint("max_steps", tp.blast_term_ite_max_steps());
            m_max_inflation = p.get_uint("max_inflation", tp.blast_term_ite_max_inflation());
        }

        bool max_steps_exceeded(unsigned num_steps) const {
            return num_steps >= m_max_steps;
        }

        br_status mk_app_core(func_decl* f, unsigned num_args, expr* const* args, expr_ref& result) {
            if (m.is_ite(f))
                return BR_FAILED;
            if (m_max_inflation < UINT_MAX &&
                m_init_term_size > 0 &&
                m_max_inflation * m_init_term_size < m_num_fresh)
                return BR_FAILED;

            for (unsigned i = 0; i < num_args; ++i) {
                expr* c, *t, *e;
                if (!m.is_bool(args[i]) && m.is_ite(args[i], c, t, e)) {
                    TRACE(blast_term_ite, result = m.mk_app(f, num_args, args); tout << result << "\n";);
                    expr_ref e1(m), e2(m);
                    ptr_vector<expr> args1(num_args, args);
                    args1[i] = t;
                    e1 = m.mk_app(f, num_args, args1.data());
                    if (m.are_equal(t, e)) {
                        result = e1;
                        return BR_REWRITE1;
                    }
                    else {
                        args1[i] = e;
                        e2 = m.mk_app(f, num_args, args1.data());
                        result = m.mk_ite(c, e1, e2);
                        ++m_num_fresh;
                        return BR_REWRITE3;
                    }
                }
            }
            return BR_FAILED;
        }

        bool rewrite_patterns() const { return false; }

        br_status reduce_app(func_decl* f, unsigned num, expr* const* args, expr_ref& result, proof_ref& result_pr) {
            return mk_app_core(f, num, args, result);
        }
    };

    struct rw : public rewriter_tpl<rw_cfg> {
        rw_cfg m_cfg;

        rw(ast_manager& m, params_ref const& p):
            rewriter_tpl<rw_cfg>(m, m.proofs_enabled(), m_cfg),
            m_cfg(m, p) {
        }
    };

    rw m_rw;

public:
    blast_term_ite_simplifier(ast_manager& m, params_ref const& p, dependent_expr_state& s):
        dependent_expr_simplifier(m, s), m_rw(m, p) {}

    char const* name() const override { return "blast-term-ite"; }

    void reduce() override {
        expr_ref new_fml(m);
        proof_ref new_pr(m);
        for (unsigned idx : indices()) {
            auto const& d = m_fmls[idx];
            if (m_rw.m_cfg.m_max_inflation < UINT_MAX) {
                m_rw.m_cfg.m_init_term_size = get_num_exprs(d.fml());
                m_rw.m_cfg.m_num_fresh = 0;
            }
            m_rw(d.fml(), new_fml, new_pr);
            if (d.fml() != new_fml)
                m_fmls.update(idx, dependent_expr(m, new_fml, mp(d.pr(), new_pr), d.dep()));
        }
    }

    static void blast_term_ite(expr_ref& fml, unsigned max_inflation) {
        ast_manager& m = fml.get_manager();
        scoped_no_proof _sp(m);
        params_ref p;
        rw ite_rw(m, p);
        ite_rw.m_cfg.m_max_inflation = max_inflation;
        if (max_inflation < UINT_MAX)
            ite_rw.m_cfg.m_init_term_size = get_num_exprs(fml);
        try {
            expr_ref tmp(m);
            ite_rw(fml, tmp);
            fml = tmp;
        }
        catch (z3_exception &) {
            // max steps exceeded.
        }
    }
};
