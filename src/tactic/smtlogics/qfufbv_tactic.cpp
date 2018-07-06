/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    qfufbv_tactic.cpp

Abstract:

    Tactic for QF_UFBV

Author:

    Leonardo (leonardo) 2012-02-27
    Mikolas Janota

Notes:

--*/
#include "tactic/tactical.h"
#include "tactic/core/simplify_tactic.h"
#include "tactic/core/propagate_values_tactic.h"
#include "tactic/core/solve_eqs_tactic.h"
#include "tactic/core/elim_uncnstr_tactic.h"
#include "smt/tactic/smt_tactic.h"
#include "tactic/bv/max_bv_sharing_tactic.h"
#include "tactic/bv/bv_size_reduction_tactic.h"
#include "tactic/core/reduce_args_tactic.h"
#include "tactic/smtlogics/qfbv_tactic.h"
#include "tactic/smtlogics/qfufbv_tactic_params.hpp"
///////////////
#include "model/model_smt2_pp.h"
#include "util/cooperate.h"
#include "ackermannization/lackr.h"
#include "ackermannization/ackermannization_params.hpp"
#include "tactic/smtlogics/qfufbv_ackr_model_converter.h"
///////////////
#include "sat/sat_solver/inc_sat_solver.h"
#include "tactic/smtlogics/qfaufbv_tactic.h"
#include "tactic/smtlogics/qfbv_tactic.h"
#include "solver/tactic2solver.h"
#include "tactic/bv/bv_bound_chk_tactic.h"
#include "ackermannization/ackermannize_bv_tactic.h"
///////////////

class qfufbv_ackr_tactic : public tactic {
public:
    qfufbv_ackr_tactic(ast_manager& m, params_ref const& p)
        : m_m(m)
        , m_p(p)
        , m_use_sat(false)
        , m_inc_use_sat(false)
    {}

    ~qfufbv_ackr_tactic() override { }

    void operator()(goal_ref const & g, goal_ref_buffer & result) override {
        ast_manager& m(g->m());
        tactic_report report("qfufbv_ackr", *g);
        fail_if_unsat_core_generation("qfufbv_ackr", g);
        fail_if_proof_generation("qfufbv_ackr", g);

        TRACE("qfufbv_ackr_tactic", g->display(tout << "goal:\n"););
        // running implementation
        ptr_vector<expr> flas;
        const unsigned sz = g->size();
        for (unsigned i = 0; i < sz; i++) flas.push_back(g->form(i));
        scoped_ptr<solver> uffree_solver = setup_sat();
        lackr imp(m, m_p, m_st, flas, uffree_solver.get());
        const lbool o = imp.operator()();
        flas.reset();
        // report result
        goal_ref resg(alloc(goal, *g, true));
        if (o == l_false) resg->assert_expr(m.mk_false());
        if (o != l_undef) result.push_back(resg.get());
        // report model
        if (g->models_enabled() && (o == l_true)) {
            model_ref abstr_model = imp.get_model();
            g->add(mk_qfufbv_ackr_model_converter(m, imp.get_info(), abstr_model));
        }
    }

    void updt_params(params_ref const & _p) override {
        qfufbv_tactic_params p(_p);
        m_use_sat = p.sat_backend();
        m_inc_use_sat = p.inc_sat_backend();
    }

    void collect_statistics(statistics & st) const override {
        ackermannization_params p(m_p);
        if (!p.eager()) st.update("lackr-its", m_st.m_it);
        st.update("ackr-constraints", m_st.m_ackrs_sz);
    }

    void reset_statistics() override { m_st.reset(); }

    void cleanup() override { }

    tactic* translate(ast_manager& m) override {
        return alloc(qfufbv_ackr_tactic, m, m_p);
    }
private:
    ast_manager&                         m_m;
    params_ref                           m_p;
    lackr_stats                          m_st;
    bool                                 m_use_sat;
    bool                                 m_inc_use_sat;

    solver* setup_sat() {
        solver * sat(nullptr);
        if (m_use_sat) {
            if (m_inc_use_sat) {
                sat = mk_inc_sat_solver(m_m, m_p);
            }
            else {
                tactic_ref t = mk_qfbv_tactic(m_m, m_p);
                sat = mk_tactic2solver(m_m, t.get(), m_p);
            }
        }
        else {
            tactic_ref t = mk_qfaufbv_tactic(m_m, m_p);
            sat = mk_tactic2solver(m_m, t.get(), m_p);
        }
        SASSERT(sat != NULL);
        sat->set_produce_models(true);
        return sat;
    }


};

static tactic * mk_qfufbv_preamble1(ast_manager & m, params_ref const & p) {
    params_ref simp2_p = p;
    simp2_p.set_bool("pull_cheap_ite", true);
    simp2_p.set_bool("push_ite_bv", false);
    simp2_p.set_bool("local_ctx", true);
    simp2_p.set_uint("local_ctx_limit", 10000000);

    simp2_p.set_bool("ite_extra_rules", true);
    simp2_p.set_bool("mul2concat", true);

    params_ref ctx_simp_p;
    ctx_simp_p.set_uint("max_depth", 32);
    ctx_simp_p.set_uint("max_steps", 5000000);

    return and_then(
        mk_simplify_tactic(m),
        mk_propagate_values_tactic(m),
        if_no_proofs(if_no_unsat_cores(mk_bv_bound_chk_tactic(m))),
        //using_params(mk_ctx_simplify_tactic(m_m), ctx_simp_p),
        mk_solve_eqs_tactic(m),
        mk_elim_uncnstr_tactic(m),
        if_no_proofs(if_no_unsat_cores(mk_bv_size_reduction_tactic(m))),
        mk_max_bv_sharing_tactic(m),
        using_params(mk_simplify_tactic(m), simp2_p)
        );
}

static tactic * mk_qfufbv_preamble(ast_manager & m, params_ref const & p) {
    return and_then(mk_simplify_tactic(m),
                    mk_propagate_values_tactic(m),
                    mk_solve_eqs_tactic(m),
                    mk_elim_uncnstr_tactic(m),
                    if_no_proofs(if_no_unsat_cores(mk_reduce_args_tactic(m))),
                    if_no_proofs(if_no_unsat_cores(mk_bv_size_reduction_tactic(m))),
                    mk_max_bv_sharing_tactic(m),
                    if_no_proofs(if_no_unsat_cores(mk_ackermannize_bv_tactic(m,p)))
                    );
}

tactic * mk_qfufbv_tactic(ast_manager & m, params_ref const & p) {
    params_ref main_p;
    main_p.set_bool("elim_and", true);
    main_p.set_bool("blast_distinct", true);

    tactic * const preamble_st = mk_qfufbv_preamble(m, p);

    tactic * st = using_params(and_then(preamble_st,
        cond(mk_is_qfbv_probe(), mk_qfbv_tactic(m), mk_smt_tactic())),
        main_p);

    st->updt_params(p);
    return st;
}

tactic * mk_qfufbv_ackr_tactic(ast_manager & m, params_ref const & p) {
    tactic * const preamble_t = mk_qfufbv_preamble1(m, p);

    tactic * const actual_tactic = alloc(qfufbv_ackr_tactic, m, p);
    return and_then(preamble_t,
        cond(mk_is_qfufbv_probe(), actual_tactic, mk_smt_tactic()));
}
