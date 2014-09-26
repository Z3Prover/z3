/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    quasi_macros_tactic.cpp

Abstract:

    Quasi-Macros

Author:

    Christoph (cwinter) 2012-10-26

Notes:

--*/
#include"tactical.h"
#include"simplifier.h"
#include"basic_simplifier_plugin.h"
#include"arith_simplifier_plugin.h"
#include"bv_simplifier_plugin.h"
#include"macro_manager.h"
#include"macro_finder.h"
#include"extension_model_converter.h"
#include"quasi_macros.h"
#include"quasi_macros_tactic.h"

class quasi_macros_tactic : public tactic {

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
            tactic_report report("quasi-macros", *g);
            fail_if_unsat_core_generation("quasi-macros", g);

            bool produce_proofs = g->proofs_enabled();
            
            simplifier simp(m_manager);
            basic_simplifier_plugin * bsimp = alloc(basic_simplifier_plugin, m_manager);
            bsimp->set_eliminate_and(true);
            simp.register_plugin(bsimp);
            arith_simplifier_params a_params;
            arith_simplifier_plugin * asimp = alloc(arith_simplifier_plugin, m_manager, *bsimp, a_params);
            simp.register_plugin(asimp);
            bv_simplifier_params bv_params;
            bv_simplifier_plugin * bvsimp = alloc(bv_simplifier_plugin, m_manager, *bsimp, bv_params);
            simp.register_plugin(bvsimp);
                
            macro_manager mm(m_manager, simp);
            quasi_macros qm(m_manager, mm, simp);
            bool more = true;
        
            expr_ref_vector forms(m_manager), new_forms(m_manager);
            proof_ref_vector proofs(m_manager), new_proofs(m_manager);

            unsigned size = g->size();
            for (unsigned i = 0; i < size; i++) {
                forms.push_back(g->form(i));
                proofs.push_back(g->pr(i));
            }
        
            while (more) { // CMW: use repeat(...) ?
                if (m_cancel) 
                  throw tactic_exception(TACTIC_CANCELED_MSG);

                new_forms.reset();
                new_proofs.reset();
                more = qm(forms.size(), forms.c_ptr(), proofs.c_ptr(), new_forms, new_proofs);            
                forms.swap(new_forms);
                proofs.swap(new_proofs);            
            }

            g->reset();
            for (unsigned i = 0; i < new_forms.size(); i++)
                g->assert_expr(new_forms.get(i), produce_proofs ? new_proofs.get(i) : 0, 0);

            extension_model_converter * evmc = alloc(extension_model_converter, mm.get_manager());
            unsigned num = mm.get_num_macros();
            for (unsigned i = 0; i < num; i++) {
                expr_ref f_interp(mm.get_manager());
                func_decl * f = mm.get_macro_interpretation(i, f_interp);
                evmc->insert(f, f_interp);
            }
            mc = evmc;

            g->inc_depth();
            result.push_back(g.get());
            TRACE("quasi-macros", g->display(tout););
            SASSERT(g->is_well_sorted());
        }

        void updt_params(params_ref const & p) {
        }
    };
    
    imp *      m_imp;
    params_ref m_params;

public:
    quasi_macros_tactic(ast_manager & m, params_ref const & p):
        m_params(p) {
        m_imp = alloc(imp, m, p);
    }

    virtual tactic * translate(ast_manager & m) {
        return alloc(quasi_macros_tactic, m, m_params);
    }
        
    virtual ~quasi_macros_tactic() {
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

tactic * mk_quasi_macros_tactic(ast_manager & m, params_ref const & p) {
    return alloc(quasi_macros_tactic, m, p);
}
