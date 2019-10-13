/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    fpa2bv_tactic.cpp

Abstract:

    Tactic that converts floating points to bit-vectors

Author:

    Christoph (cwinter) 2012-02-09

Notes:

--*/
#include "tactic/tactical.h"
#include "ast/fpa/fpa2bv_rewriter.h"
#include "tactic/core/simplify_tactic.h"
#include "tactic/fpa/fpa2bv_tactic.h"
#include "tactic/fpa/fpa2bv_model_converter.h"

class fpa2bv_tactic : public tactic {
    struct imp {
        ast_manager &     m;
        fpa2bv_converter  m_conv;
        fpa2bv_rewriter   m_rw;
        unsigned          m_num_steps;

        bool              m_proofs_enabled;
        bool              m_produce_models;
        bool              m_produce_unsat_cores;

        imp(ast_manager & _m, params_ref const & p):
            m(_m),
            m_conv(m),
            m_rw(m, m_conv, p),
            m_proofs_enabled(false),
            m_produce_models(false),
            m_produce_unsat_cores(false) {
            }

        void updt_params(params_ref const & p) {
            m_rw.cfg().updt_params(p);
        }

        void operator()(goal_ref const & g,
                        goal_ref_buffer & result) {
            SASSERT(g->is_well_sorted());
            m_proofs_enabled      = g->proofs_enabled();
            m_produce_models      = g->models_enabled();
            m_produce_unsat_cores = g->unsat_core_enabled();

            result.reset();
            tactic_report report("fpa2bv", *g);
            m_rw.reset();

            TRACE("fpa2bv", tout << "BEFORE: " << std::endl; g->display(tout););

            if (g->inconsistent()) {
                result.push_back(g.get());
                return;
            }

            m_num_steps = 0;
            expr_ref   new_curr(m);
            proof_ref  new_pr(m);
            unsigned size = g->size();
            for (unsigned idx = 0; idx < size; idx++) {
                if (g->inconsistent())
                    break;
                expr * curr = g->form(idx);
                m_rw(curr, new_curr, new_pr);
                m_num_steps += m_rw.get_num_steps();
                if (m_proofs_enabled) {
                    proof * pr = g->pr(idx);
                    new_pr     = m.mk_modus_ponens(pr, new_pr);
                }
                g->update(idx, new_curr, new_pr, g->dep(idx));

                if (is_app(new_curr)) {
                    const app * a = to_app(new_curr.get());
                    if (a->get_family_id() == m_conv.fu().get_family_id() &&
                        a->get_decl_kind() == OP_FPA_IS_NAN) {
                        // Inject auxiliary lemmas that fix e to the one and only NaN value,
                        // that is (= e (fp #b0 #b1...1 #b0...01)), so that the value propagation
                        // has a value to propagate.
                        expr_ref sgn(m), sig(m), exp(m);
                        m_conv.split_fp(new_curr, sgn, exp, sig);
                        result.back()->assert_expr(m.mk_eq(sgn, m_conv.bu().mk_numeral(0, 1)));
                        result.back()->assert_expr(m.mk_eq(exp, m_conv.bu().mk_bv_neg(m_conv.bu().mk_numeral(1, m_conv.bu().get_bv_size(exp)))));
                        result.back()->assert_expr(m.mk_eq(sig, m_conv.bu().mk_numeral(1, m_conv.bu().get_bv_size(sig))));
                    }
                }
            }

            if (g->models_enabled())
                g->add(mk_fpa2bv_model_converter(m, m_conv));

            g->inc_depth();
            result.push_back(g.get());

            for (unsigned i = 0; i < m_conv.m_extra_assertions.size(); i++)
                result.back()->assert_expr(m_conv.m_extra_assertions[i].get());

            SASSERT(g->is_well_sorted());
            TRACE("fpa2bv", tout << "AFTER: " << std::endl; g->display(tout);
                  if (g->mc()) g->mc()->display(tout); tout << std::endl; );
        }
    };

    imp *      m_imp;
    params_ref m_params;

public:
    fpa2bv_tactic(ast_manager & m, params_ref const & p):
        m_params(p) {
        m_imp = alloc(imp, m, p);
    }

    tactic * translate(ast_manager & m) override {
        return alloc(fpa2bv_tactic, m, m_params);
    }

    ~fpa2bv_tactic() override {
        dealloc(m_imp);
    }

    void updt_params(params_ref const & p) override {
        m_params = p;
        m_imp->updt_params(p);
    }

    void collect_param_descrs(param_descrs & r) override {
    }

    void operator()(goal_ref const & in,
                    goal_ref_buffer & result) override {
        try {
            (*m_imp)(in, result);
        }
        catch (rewriter_exception & ex) {
            throw tactic_exception(ex.msg());
        }
    }

    void cleanup() override {
        imp * d = alloc(imp, m_imp->m, m_params);
        std::swap(d, m_imp);
        dealloc(d);
    }

};

tactic * mk_fpa2bv_tactic(ast_manager & m, params_ref const & p) {
    return clean(alloc(fpa2bv_tactic, m, p));
}
