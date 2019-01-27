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
#include "tactic/tactical.h"
#include "tactic/core/cofactor_elim_term_ite.h"

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
            g.update(i, new_f, nullptr, g.dep(i));
        }
    }

public:
    cofactor_term_ite_tactic(ast_manager & m, params_ref const & p):
        m_params(p),
        m_elim_ite(m, p) {
    }

    tactic * translate(ast_manager & m) override {
        return alloc(cofactor_term_ite_tactic, m, m_params);
    }

    ~cofactor_term_ite_tactic() override {}
    void updt_params(params_ref const & p) override { m_params = p; m_elim_ite.updt_params(p); }
    void collect_param_descrs(param_descrs & r) override { m_elim_ite.collect_param_descrs(r); }
    
    void  operator()(goal_ref const & g, goal_ref_buffer& result) override {
        SASSERT(g->is_well_sorted());
        fail_if_proof_generation("cofactor-term-ite", g);
        fail_if_unsat_core_generation("cofactor-term-ite", g);
        tactic_report report("cofactor-term-ite", *g);
        process(*(g.get()));
        g->inc_depth();
        result.push_back(g.get());
        TRACE("cofactor-term-ite", g->display(tout););
        SASSERT(g->is_well_sorted());
    }
    
    void cleanup() override { return m_elim_ite.cleanup(); }

};

tactic * mk_cofactor_term_ite_tactic(ast_manager & m, params_ref const & p) {
    return clean(alloc(cofactor_term_ite_tactic, m, p));
}
