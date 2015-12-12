/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    der_tactic.cpp

Abstract:

    DER tactic

Author:

    Leonardo de Moura (leonardo) 2012-10-20

--*/
#include"der.h"
#include"tactical.h"

class der_tactic : public tactic {
    struct imp {
        ast_manager &   m_manager;
        der_rewriter    m_r;
        
        imp(ast_manager & m):
            m_manager(m),
            m_r(m) {
        }
        
        ast_manager & m() const { return m_manager; }
                
        void reset() {
            m_r.reset();
        }
        
        void operator()(goal & g) {
            SASSERT(g.is_well_sorted());
            bool proofs_enabled = g.proofs_enabled();
            tactic_report report("der", g);
            TRACE("before_der", g.display(tout););
            expr_ref   new_curr(m());
            proof_ref  new_pr(m());
            unsigned size = g.size();
            for (unsigned idx = 0; idx < size; idx++) {
                if (g.inconsistent())
                    break;
                expr * curr = g.form(idx);
                m_r(curr, new_curr, new_pr);
                if (proofs_enabled) {
                    proof * pr = g.pr(idx);
                    new_pr     = m().mk_modus_ponens(pr, new_pr);
                }
                g.update(idx, new_curr, new_pr, g.dep(idx));
            }
            g.elim_redundancies();
            TRACE("after_der", g.display(tout););
            SASSERT(g.is_well_sorted());
        }
    };

    imp *      m_imp;

public:
    der_tactic(ast_manager & m) {
        m_imp = alloc(imp, m);
    }

    virtual tactic * translate(ast_manager & m) {
        return alloc(der_tactic, m);
    }

    virtual ~der_tactic() {
        dealloc(m_imp);
    }
    
    virtual void operator()(goal_ref const & in, 
                            goal_ref_buffer & result, 
                            model_converter_ref & mc, 
                            proof_converter_ref & pc,
                            expr_dependency_ref & core) {
        mc = 0; pc = 0; core = 0;
        (*m_imp)(*(in.get()));
        in->inc_depth();
        result.push_back(in.get());
    }

    virtual void cleanup() {
        ast_manager & m = m_imp->m();
        imp * d = alloc(imp, m);
        std::swap(d, m_imp);        
        dealloc(d);
    }
    
};

tactic * mk_der_tactic(ast_manager & m) {
    return alloc(der_tactic, m);
}
