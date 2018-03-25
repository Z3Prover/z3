/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    bvarray2uf_tactic.cpp

Abstract:

    Tactic that rewrites bit-vector arrays into bit-vector
    (uninterpreted) functions.

Author:

    Christoph (cwinter) 2015-11-04

Notes:

--*/
#include "tactic/tactical.h"
#include "ast/bv_decl_plugin.h"
#include "ast/rewriter/expr_replacer.h"
#include "tactic/generic_model_converter.h"
#include "ast/ast_smt2_pp.h"

#include "tactic/bv/bvarray2uf_tactic.h"
#include "tactic/bv/bvarray2uf_rewriter.h"

class bvarray2uf_tactic : public tactic {

    struct imp {
        ast_manager &       m_manager;
        bool                m_produce_models;
        bool                m_produce_proofs;
        bool                m_produce_cores;
        bvarray2uf_rewriter m_rw;

        ast_manager & m() { return m_manager; }

        imp(ast_manager & m, params_ref const & p) :
            m_manager(m),
            m_produce_models(false),
            m_produce_proofs(false),
            m_produce_cores(false),
            m_rw(m, p) {
            updt_params(p);
        }


        void checkpoint() {
            if (m_manager.canceled())
                throw tactic_exception(m_manager.limit().get_cancel_msg());
        }

        void operator()(goal_ref const & g,
                        goal_ref_buffer & result)
        {
            SASSERT(g->is_well_sorted());
            tactic_report report("bvarray2uf", *g);
            result.reset();
            fail_if_unsat_core_generation("bvarray2uf", g);

            TRACE("bvarray2uf", tout << "Before: " << std::endl; g->display(tout); );
            m_produce_models = g->models_enabled();
            model_converter_ref mc;

            if (m_produce_models) {
                generic_model_converter * fmc = alloc(generic_model_converter, m_manager, "bvarray2uf");
                mc = fmc;
                m_rw.set_mcs(fmc);
            }


            m_rw.reset();
            expr_ref   new_curr(m_manager);
            proof_ref  new_pr(m_manager);
            unsigned size = g->size();
            for (unsigned idx = 0; idx < size; idx++) {
                if (g->inconsistent())
                    break;
                expr * curr = g->form(idx);
                m_rw(curr, new_curr, new_pr);
                if (m_produce_proofs) {
                    proof * pr = g->pr(idx);
                    new_pr = m_manager.mk_modus_ponens(pr, new_pr);
                }
                g->update(idx, new_curr, new_pr, g->dep(idx));
            }

            for (unsigned i = 0; i < m_rw.m_cfg.extra_assertions.size(); i++)
                g->assert_expr(m_rw.m_cfg.extra_assertions[i].get());

            g->inc_depth();
            g->add(mc.get());
            result.push_back(g.get());
            TRACE("bvarray2uf", tout << "After: " << std::endl; g->display(tout););
            SASSERT(g->is_well_sorted());
        }

        void updt_params(params_ref const & p) {
        }
    };

    imp *      m_imp;
    params_ref m_params;

public:
    bvarray2uf_tactic(ast_manager & m, params_ref const & p) :
        m_params(p) {
        m_imp = alloc(imp, m, p);
    }

    tactic * translate(ast_manager & m) override {
        return alloc(bvarray2uf_tactic, m, m_params);
    }

    ~bvarray2uf_tactic() override {
        dealloc(m_imp);
    }

    void updt_params(params_ref const & p) override {
        m_params = p;
        m_imp->updt_params(p);
    }

    void collect_param_descrs(param_descrs & r) override {
        insert_produce_models(r);
    }

    void operator()(goal_ref const & in,
                    goal_ref_buffer & result) override {
        (*m_imp)(in, result);
    }

    void cleanup() override {
        ast_manager & m = m_imp->m();
        imp * d = alloc(imp, m, m_params);
        std::swap(d, m_imp);
        dealloc(d);
    }

};


tactic * mk_bvarray2uf_tactic(ast_manager & m, params_ref const & p) {
    return clean(alloc(bvarray2uf_tactic, m, p));
}
