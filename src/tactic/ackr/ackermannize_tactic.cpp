/*++
Copyright (c) 2016 Microsoft Corporation

Module Name:

ackermannize_tactic.cpp

Abstract:

Author:

Mikolas Janota

Revision History:
--*/
#include"tactical.h"
#include"lackr.h"
#include"ackr_params.hpp"
#include"ackr_model_converter.h"
#include"model_smt2_pp.h"

class ackermannize_tactic : public tactic {
public:
    ackermannize_tactic(ast_manager& m, params_ref const& p)
        : m_m(m)
        , m_p(p)
    {}

    virtual ~ackermannize_tactic() { }

    virtual void operator()(goal_ref const & g,
        goal_ref_buffer & result,
        model_converter_ref & mc,
        proof_converter_ref & pc,
        expr_dependency_ref & core) {
        mc = 0;
        ast_manager& m(g->m());
        expr_ref_vector flas(m);
        const unsigned sz = g->size();
        for (unsigned i = 0; i < sz; i++) flas.push_back(g->form(i));
        scoped_ptr<lackr> imp = alloc(lackr, m, m_p, m_st, flas, NULL);
        flas.reset();
        // mk result
        goal_ref resg(alloc(goal, *g, true));
        imp->mk_ackermann(resg);
        result.push_back(resg.get());
        // report model
        if (g->models_enabled()) {
            mc = mk_ackr_model_converter(m, imp->get_info());
        }
    }

    virtual void collect_statistics(statistics & st) const {
        st.update("ackr-constraints", m_st.m_ackrs_sz);
    }

    virtual void reset_statistics() { m_st.reset(); }

    virtual void cleanup() { }

    virtual tactic* translate(ast_manager& m) {
        return alloc(ackermannize_tactic, m, m_p);
    }
private:
    ast_manager&                         m_m;
    params_ref                           m_p;
    lackr_stats                          m_st;
};

tactic * mk_ackermannize_tactic(ast_manager & m, params_ref const & p) {
    return alloc(ackermannize_tactic, m, p);
}
