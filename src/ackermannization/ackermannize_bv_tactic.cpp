/*++
Copyright (c) 2016 Microsoft Corporation

Module Name:

ackermannize_bv_tactic.cpp

Abstract:

Author:

Mikolas Janota

Revision History:
--*/
#include "ackermannization/ackermannize_bv_tactic.h"
#include "tactic/tactical.h"
#include "ackermannization/lackr.h"
#include "model/model_smt2_pp.h"
#include "ackermannization/ackermannize_bv_tactic_params.hpp"
#include "ackermannization/ackermannize_bv_model_converter.h"


class ackermannize_bv_tactic : public tactic {
public:
    ackermannize_bv_tactic(ast_manager& m, params_ref const& p)
        : m(m), m_p(p)
    {
        updt_params(p);
    }

    ~ackermannize_bv_tactic() override { }

    void operator()(goal_ref const & g, goal_ref_buffer & result) override {
        tactic_report report("ackermannize", *g);
        fail_if_unsat_core_generation("ackermannize", g);
        fail_if_proof_generation("ackermannize", g);
        TRACE("ackermannize", g->display(tout << "in\n"););

        ptr_vector<expr> flas;
        const unsigned sz = g->size();
        for (unsigned i = 0; i < sz; i++) flas.push_back(g->form(i));
        lackr lackr(m, m_p, m_st, flas, nullptr);

        // mk result
        goal_ref resg(alloc(goal, *g, true));
        const bool success = lackr.mk_ackermann(resg, m_lemma_limit);
        if (!success) { // Just pass on the input unchanged
            TRACE("ackermannize", tout << "ackermannize not run due to limit" << std::endl;);
            result.reset();
            result.push_back(g.get());
            return;
        }
        result.push_back(resg.get());
        // report model
        if (g->models_enabled()) {
            resg->add(mk_ackermannize_bv_model_converter(m, lackr.get_info()));
        }
        
        resg->inc_depth();
        TRACE("ackermannize", resg->display(tout << "out\n"););
        SASSERT(resg->is_well_sorted());
    }


    void updt_params(params_ref const & _p) override {
        ackermannize_bv_tactic_params p(_p);
        m_lemma_limit = p.div0_ackermann_limit();
    }

    void collect_param_descrs(param_descrs & r) override {
        ackermannize_bv_tactic_params::collect_param_descrs(r);
    }

    void collect_statistics(statistics & st) const override {
        st.update("ackr-constraints", m_st.m_ackrs_sz);
    }

    void reset_statistics() override { m_st.reset(); }

    void cleanup() override { }

    tactic* translate(ast_manager& m) override {
        return alloc(ackermannize_bv_tactic, m, m_p);
    }
private:
    ast_manager&                         m;
    params_ref                           m_p;
    lackr_stats                          m_st;
    double                               m_lemma_limit;
};

tactic * mk_ackermannize_bv_tactic(ast_manager & m, params_ref const & p) {
    return alloc(ackermannize_bv_tactic, m, p);
}
