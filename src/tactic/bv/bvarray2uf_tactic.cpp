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
#include"tactical.h"
#include"bv_decl_plugin.h"
#include"expr_replacer.h"
#include"extension_model_converter.h"
#include"filter_model_converter.h"
#include"ast_smt2_pp.h"

#include"bvarray2uf_tactic.h"
#include"bvarray2uf_rewriter.h"

class bvarray2uf_tactic : public tactic {

    struct imp {
        ast_manager &       m_manager;
        bool                m_produce_models;
        bool                m_produce_proofs;
        bool                m_produce_cores;
        volatile bool       m_cancel;
        bvarray2uf_rewriter m_rw;

        ast_manager & m() { return m_manager; }

        imp(ast_manager & m, params_ref const & p) :
            m_manager(m),
            m_produce_models(false),
            m_produce_proofs(false),
            m_produce_cores(false),
            m_cancel(false),
            m_rw(m, p) {
            updt_params(p);
        }

        void set_cancel(bool f) {
            m_cancel = f;
        }

        void checkpoint() {
            if (m_cancel)
                throw tactic_exception(TACTIC_CANCELED_MSG);
        }

        void operator()(goal_ref const & g,
                        goal_ref_buffer & result,
                        model_converter_ref & mc,
                        proof_converter_ref & pc,
                        expr_dependency_ref & core)
        {
            SASSERT(g->is_well_sorted());
            tactic_report report("bvarray2uf", *g);
            mc = 0; pc = 0; core = 0; result.reset();
            fail_if_proof_generation("bvarray2uf", g);
            fail_if_unsat_core_generation("bvarray2uf", g);

            TRACE("bvarray2uf", tout << "Before: " << std::endl; g->display(tout); );
            m_produce_models = g->models_enabled();

            if (m_produce_models) {
                extension_model_converter * emc = alloc(extension_model_converter, m_manager);
                filter_model_converter * fmc = alloc(filter_model_converter, m_manager);
                mc = concat(emc, fmc);
                m_rw.set_mcs(emc, fmc);

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
                //if (m_produce_proofs) {
                //    proof * pr = g->pr(idx);
                //    new_pr = m.mk_modus_ponens(pr, new_pr);
                //}
                g->update(idx, new_curr, new_pr, g->dep(idx));
            }

            for (unsigned i = 0; i < m_rw.m_cfg.extra_assertions.size(); i++)
                g->assert_expr(m_rw.m_cfg.extra_assertions[i].get());

            g->inc_depth();
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

    virtual tactic * translate(ast_manager & m) {
        return alloc(bvarray2uf_tactic, m, m_params);
    }

    virtual ~bvarray2uf_tactic() {
        dealloc(m_imp);
    }

    virtual void updt_params(params_ref const & p) {
        m_params = p;
        m_imp->updt_params(p);
    }

    virtual void collect_param_descrs(param_descrs & r) {
        insert_produce_models(r);
    }

    virtual void operator()(goal_ref const & in,
                            goal_ref_buffer & result,
                            model_converter_ref & mc,
                            proof_converter_ref & pc,
                            expr_dependency_ref & core) {
        (*m_imp)(in, result, mc, pc, core);
    }

    virtual void cleanup() {
        ast_manager & m = m_imp->m();
        imp * d = alloc(imp, m, m_params);
    #pragma omp critical (tactic_cancel)
        {
            std::swap(d, m_imp);
        }
        dealloc(d);
    }

    virtual void set_cancel(bool f) {
        if (m_imp)
            m_imp->set_cancel(f);
    }

};


tactic * mk_bvarray2uf_tactic(ast_manager & m, params_ref const & p) {
    return clean(alloc(bvarray2uf_tactic, m, p));
}
