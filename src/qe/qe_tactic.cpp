/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    qe_tactic.cpp

Abstract:

    Quantifier elimination front-end for tactic framework.

Author:

    Leonardo de Moura (leonardo) 2011-12-28.

Revision History:

--*/
#include"tactical.h"
#include"filter_model_converter.h"
#include"cooperate.h"
#include"qe.h"

class qe_tactic : public tactic {
    statistics               m_st;
    struct     imp {
        ast_manager &            m;
        smt_params               m_fparams;
        qe::expr_quant_elim      m_qe;

        imp(ast_manager & _m, params_ref const & p):
            m(_m),
            m_qe(m, m_fparams) {
            updt_params(p);
        }

        void updt_params(params_ref const & p) {
            m_fparams.updt_params(p);
            m_fparams.m_nlquant_elim = p.get_bool("qe_nonlinear", false);
            m_qe.updt_params(p);
        }

        void collect_param_descrs(param_descrs & r) {
            m_qe.collect_param_descrs(r);
        }

        void checkpoint() {
            if (m.canceled()) 
                throw tactic_exception(m.limit().get_cancel_msg());
            cooperate("qe");
        }

        void operator()(goal_ref const & g, 
                        goal_ref_buffer & result, 
                        model_converter_ref & mc, 
                        proof_converter_ref & pc,
                        expr_dependency_ref & core) {
            SASSERT(g->is_well_sorted());
            mc = 0; pc = 0; core = 0;
            tactic_report report("qe", *g);
            m_fparams.m_model = g->models_enabled();
            proof_ref new_pr(m);
            expr_ref new_f(m);
            bool produce_proofs = g->proofs_enabled();

            unsigned sz = g->size();
            for (unsigned i = 0; i < sz; i++) {
                checkpoint();
                if (g->inconsistent())
                    break;
                expr * f = g->form(i);
                if (!has_quantifiers(f))
                    continue;
                m_qe(m.mk_true(), f, new_f);
                new_pr = 0;
                if (produce_proofs) {
                    new_pr = m.mk_modus_ponens(g->pr(i), new_pr);
                }
                g->update(i, new_f, new_pr, g->dep(i));                
            }
            g->inc_depth();
            g->elim_true();
            result.push_back(g.get());
            TRACE("qe", g->display(tout););
            SASSERT(g->is_well_sorted());
        }

        void collect_statistics(statistics & st) const {
            m_qe.collect_statistics(st);
        }

        void reset_statistics() {            
        }

    };
    
    imp *      m_imp;
    params_ref m_params;
public:
    qe_tactic(ast_manager & m, params_ref const & p):
        m_params(p) {
        m_imp = alloc(imp, m, p);
    }

    virtual tactic * translate(ast_manager & m) {
        return alloc(qe_tactic, m, m_params);
    }
        
    virtual ~qe_tactic() {
        dealloc(m_imp);
    }

    virtual void updt_params(params_ref const & p) {
        m_params = p;
        m_imp->updt_params(p);
    }

   
    virtual void collect_param_descrs(param_descrs & r) {
        r.insert("qe_nonlinear", CPK_BOOL, "(default: false) enable virtual term substitution.");
        m_imp->collect_param_descrs(r);
    }
    
    virtual void operator()(goal_ref const & in, 
                            goal_ref_buffer & result, 
                            model_converter_ref & mc, 
                            proof_converter_ref & pc,
                            expr_dependency_ref & core) {
        (*m_imp)(in, result, mc, pc, core);
        m_st.reset();
        m_imp->collect_statistics(m_st);
        
    }

    virtual void collect_statistics(statistics & st) const {
        st.copy(m_st);
    }

    virtual void reset_statistics() {
        m_st.reset();
    }

    
    virtual void cleanup() {
        ast_manager & m = m_imp->m;
        dealloc(m_imp);
        m_imp = alloc(imp, m, m_params);
    }
    
};

tactic * mk_qe_tactic(ast_manager & m, params_ref const & p) {
    return clean(alloc(qe_tactic, m, p));
}

