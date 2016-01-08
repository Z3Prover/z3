/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

lackr_tactic.cpp

Abstract:

Author:

Mikolas Janota

Revision History:
--*/
#include"tactical.h"
///////////////
#include"solve_eqs_tactic.h"
#include"simplify_tactic.h"
#include"propagate_values_tactic.h"
#include"bit_blaster_tactic.h"
#include"elim_uncnstr_tactic.h"
#include"max_bv_sharing_tactic.h"
#include"bv_size_reduction_tactic.h"
#include"ctx_simplify_tactic.h"
#include"nnf_tactic.h"
///////////////
#include"model_smt2_pp.h"
#include"cooperate.h"
#include"lackr.h"
#include"ackr_params.hpp"
#include"lackr_model_converter.h"

class lackr_tactic : public tactic {
public:
    lackr_tactic(ast_manager& m, params_ref const& p)
        : m_m(m)
        , m_p(p)
    {}

    virtual ~lackr_tactic() { }

    virtual void operator()(goal_ref const & g,
        goal_ref_buffer & result,
        model_converter_ref & mc,
        proof_converter_ref & pc,
        expr_dependency_ref & core) {
        mc = 0;
        ast_manager& m(g->m());
        TRACE("lackr", g->display(tout << "Goal:\n"););
        // conflate all assertions into one conjunction
        ptr_vector<expr> flas;
        g->get_formulas(flas);
        expr_ref f(m);
        f = m.mk_and(flas.size(), flas.c_ptr());
        // running implementation
        scoped_ptr<lackr> imp = alloc(lackr, m, m_p, m_st, f);
        const lbool o = imp->operator()();
        flas.reset();
        // report result
        goal_ref resg(alloc(goal, *g, true));
        if (o == l_false) resg->assert_expr(m.mk_false());
        if (o != l_undef) result.push_back(resg.get());
        // report model
        if (g->models_enabled() && (o == l_true)) {
            model_ref abstr_model = imp->get_model();
            mc = mk_lackr_model_converter(m, imp->get_info(), abstr_model);
        }
    }

    virtual void collect_statistics(statistics & st) const {
        ackr_params p(m_p);       
        if (!p.eager()) st.update("lackr-its", m_st.m_it);
        st.update("ackr-constraints", m_st.m_ackrs_sz);
    }

    virtual void reset_statistics() { m_st.reset(); }

    virtual void cleanup() { }

    virtual tactic* translate(ast_manager& m) {
        return alloc(lackr_tactic, m, m_p);
    }
private:
    ast_manager&                         m_m;
    params_ref                           m_p;
    lackr_stats                          m_st;
};

tactic * mk_lackr_tactic(ast_manager & m, params_ref const & p) {
    //return and_then(mk_nnf_tactic(m_m, m_p), alloc(lackr_tactic, m_m, m_p));
    //return alloc(lackr_tactic, m_m, m_p);
    //params_ref main_p;
    //main_p.set_bool("elim_and", true);
    //main_p.set_bool("sort_store", true);
    //main_p.set_bool("expand_select_store", true);
    //main_p.set_bool("expand_store_eq", true);

    params_ref simp2_p = p;
    simp2_p.set_bool("som", true);
    simp2_p.set_bool("pull_cheap_ite", true);
    simp2_p.set_bool("push_ite_bv", false);
    simp2_p.set_bool("local_ctx", true);
    simp2_p.set_uint("local_ctx_limit", 10000000);

    simp2_p.set_bool("ite_extra_rules", true);
    //simp2_p.set_bool("blast_eq_value", true);
    //simp2_p.set_bool("bv_sort_ac", true);

    params_ref ctx_simp_p;
    ctx_simp_p.set_uint("max_depth", 32);
    ctx_simp_p.set_uint("max_steps", 5000000);

    tactic * const preamble_t = and_then(
        mk_simplify_tactic(m),
        mk_propagate_values_tactic(m),
        //using_params(mk_ctx_simplify_tactic(m_m), ctx_simp_p),
        mk_solve_eqs_tactic(m),
        mk_elim_uncnstr_tactic(m),
        if_no_proofs(if_no_unsat_cores(mk_bv_size_reduction_tactic(m))),       
        mk_max_bv_sharing_tactic(m),
        //mk_macro_finder_tactic(m, p),
        using_params(mk_simplify_tactic(m), simp2_p)
        //, mk_simplify_tactic(m)
        //mk_nnf_tactic(m_m, m_p)
        );

    return and_then(
        preamble_t,
        alloc(lackr_tactic, m, p));
}
