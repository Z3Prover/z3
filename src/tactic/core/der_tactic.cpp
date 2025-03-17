/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    der_tactic.cpp

Abstract:

    DER tactic

Author:

    Leonardo de Moura (leonardo) 2012-10-20

--*/
#include "ast/rewriter/der.h"
#include "tactic/tactical.h"

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
            tactic_report report("der", g);
            expr_ref   new_curr(m());
            proof_ref  new_pr(m());
            unsigned idx = 0;
            for (auto [curr, dep, pr] : g) {
                if (g.inconsistent())
                    break;
                m_r(curr, new_curr, new_pr);
                new_pr = m().mk_modus_ponens(pr, new_pr);                
                g.update(idx++, new_curr, new_pr, dep);
            }
            g.elim_redundancies();
        }
    };

    imp *      m_imp;

public:
    der_tactic(ast_manager & m) {
        m_imp = alloc(imp, m);
    }

    tactic * translate(ast_manager & m) override {
        return alloc(der_tactic, m);
    }

    ~der_tactic() override {
        dealloc(m_imp);
    }

    char const* name() const override { return "der"; }
    
    void operator()(goal_ref const & in, 
                    goal_ref_buffer & result) override {
        (*m_imp)(*(in.get()));
        in->inc_depth();
        result.push_back(in.get());
    }

    void cleanup() override {
        ast_manager & m = m_imp->m();
        imp * d = alloc(imp, m);
        std::swap(d, m_imp);        
        dealloc(d);
    }
    
};

tactic * mk_der_tactic(ast_manager & m) {
    return alloc(der_tactic, m);
}
