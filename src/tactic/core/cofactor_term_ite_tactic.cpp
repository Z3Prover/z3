/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    cofactor_term_ite_tactic.cpp

Abstract:

    Wrap cofactor_elim_term_ite as a tactic.
    Eliminate (ground) term if-then-else's using cofactors.

Author:

    Leonardo de Moura (leonardo) 2012-02-20.

Revision History:

--*/
#include"tactical.h"
#include"cofactor_elim_term_ite.h"

/**
   \brief Wrapper for applying cofactor_elim_term_ite in an assertion set.
 */
class cofactor_term_ite_tactic : public tactic {
    params_ref             m_params;
    cofactor_elim_term_ite m_elim_ite;

    void process(goal & g) {
        ast_manager & m = g.m();
        unsigned sz = g.size();
        for (unsigned i = 0; i < sz; i++) {
            if (g.inconsistent())
                break;
            expr * f = g.form(i);
            expr_ref new_f(m);
            m_elim_ite(f, new_f);
            g.update(i, new_f);
        }
    }

public:
    cofactor_term_ite_tactic(ast_manager & m, params_ref const & p):
        m_params(p),
        m_elim_ite(m, p) {
    }

    virtual tactic * translate(ast_manager & m) {
        return alloc(cofactor_term_ite_tactic, m, m_params);
    }

    virtual ~cofactor_term_ite_tactic() {}
    virtual void updt_params(params_ref const & p) { m_params = p; m_elim_ite.updt_params(p); }
    virtual void collect_param_descrs(param_descrs & r) { m_elim_ite.collect_param_descrs(r); }
    
    virtual void operator()(goal_ref const & g, 
                            goal_ref_buffer & result, 
                            model_converter_ref & mc, 
                            proof_converter_ref & pc,
                            expr_dependency_ref & core) {
        SASSERT(g->is_well_sorted());
        fail_if_proof_generation("cofactor-term-ite", g);
        fail_if_unsat_core_generation("cofactor-term-ite", g);
        tactic_report report("cofactor-term-ite", *g);
        mc = 0; pc = 0; core = 0;
        process(*(g.get()));
        g->inc_depth();
        result.push_back(g.get());
        TRACE("cofactor-term-ite", g->display(tout););
        SASSERT(g->is_well_sorted());
    }
    
    virtual void cleanup() { return m_elim_ite.cleanup(); }

    virtual void set_cancel(bool f) { m_elim_ite.set_cancel(f); }
};

tactic * mk_cofactor_term_ite_tactic(ast_manager & m, params_ref const & p) {
    return clean(alloc(cofactor_term_ite_tactic, m, p));
}
