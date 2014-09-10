/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    ufbv_rewriter_tactic.cpp

Abstract:

    UFBV Rewriter (demodulator)

Author:

    Christoph (cwinter) 2012-10-26

Notes:

--*/
#include"tactical.h"
#include"simplifier.h"
#include"basic_simplifier_plugin.h"
#include"ufbv_rewriter.h"
#include"ufbv_rewriter_tactic.h"

class ufbv_rewriter_tactic : public tactic {

    struct imp {
        ast_manager & m_manager;
        bool m_cancel;

        imp(ast_manager & m, params_ref const & p) : m_manager(m),m_cancel(false) {
            updt_params(p);
        }
        
        ast_manager & m() const { return m_manager; }
        
        void set_cancel(bool f) {
            m_cancel = f;
        }
        
        void operator()(goal_ref const & g, 
                        goal_ref_buffer & result, 
                        model_converter_ref & mc, 
                        proof_converter_ref & pc,
                        expr_dependency_ref & core) {
            SASSERT(g->is_well_sorted());
            mc = 0; pc = 0; core = 0;
            tactic_report report("ufbv-rewriter", *g);
            fail_if_unsat_core_generation("ufbv-rewriter", g);

            bool produce_proofs = g->proofs_enabled();
            
            basic_simplifier_plugin bsimp(m_manager);
            bsimp.set_eliminate_and(true);
            ufbv_rewriter dem(m_manager, bsimp);
            
            expr_ref_vector forms(m_manager), new_forms(m_manager);
            proof_ref_vector proofs(m_manager), new_proofs(m_manager);

            unsigned size = g->size();
            for (unsigned i = 0; i < size; i++) {
                forms.push_back(g->form(i));
                proofs.push_back(g->pr(i));
            }

            dem(forms.size(), forms.c_ptr(), proofs.c_ptr(), new_forms, new_proofs);
        
            g->reset();
            for (unsigned i = 0; i < new_forms.size(); i++)
                g->assert_expr(new_forms.get(i), produce_proofs ? new_proofs.get(i) : 0, 0);

            mc = 0; // CMW: Remark: The demodulator could potentially remove all references to a variable. 

            g->inc_depth();
            result.push_back(g.get());
            TRACE("ufbv-rewriter", g->display(tout););
            SASSERT(g->is_well_sorted());
        }

        void updt_params(params_ref const & p) {
        }
    };
    
    imp *      m_imp;
    params_ref m_params;

public:
    ufbv_rewriter_tactic(ast_manager & m, params_ref const & p):
        m_params(p) {
        m_imp = alloc(imp, m, p);
    }

    virtual tactic * translate(ast_manager & m) {
        return alloc(ufbv_rewriter_tactic, m, m_params);
    }
        
    virtual ~ufbv_rewriter_tactic() {
        dealloc(m_imp);
    }

    virtual void updt_params(params_ref const & p) {
        m_params = p;
        m_imp->updt_params(p);
    }

    virtual void collect_param_descrs(param_descrs & r) {
        insert_max_memory(r);
        insert_produce_models(r);
        insert_produce_proofs(r);
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

tactic * mk_ufbv_rewriter_tactic(ast_manager & m, params_ref const & p) {
    return alloc(ufbv_rewriter_tactic, m, p);
}
