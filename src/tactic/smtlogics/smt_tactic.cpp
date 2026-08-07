/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    smt_tactic.cpp

Abstract:

    Tactic that selects SMT backend.

Author:

    Nikolaj Bjorner (nbjorner) 2020-09-14


--*/
#include "params/sat_params.hpp"
#include "params/smt_params_helper.hpp"
#include "solver/solver2tactic.h"
#include "solver/solver.h"
#include "smt/tactic/smt_tactic_core.h"
#include "sat/tactic/sat_tactic.h"
#include "tactic/tactical.h"

namespace {

constexpr unsigned linprobe_timeout_ms = 100;

params_ref probe_params(params_ref const& p) {
    params_ref r = p;
    r.set_bool("auto_config", false);
    r.set_bool("parallel.enable", false);
    r.set_uint("arith.solver", 6);
    r.set_bool("arith.nl.linprobe", true);
    r.set_bool("arith.nl.linprobe_mode", true);
    r.set_bool("arith.nl.propagate_fixed_rows", true);
    r.set_bool("arith.nl.propagate_linear_monomials", true);
    r.set_bool("arith.nl.optimize_bounds", false);
    r.set_bool("arith.nl.grobner", false);
    r.set_bool("arith.nl.horner", false);
    r.set_bool("arith.nl.cross_nested", false);
    r.set_bool("arith.nl.nra", false);
    r.set_bool("arith.nl.nra_check_assignment", false);
    r.set_bool("arith.nl.branching", false);
    r.set_bool("arith.nl.order", false);
    r.set_bool("arith.nl.tangents", false);
    r.set_bool("arith.nl.monomial_sandwich", false);
    r.set_bool("arith.nl.monomial_binomial_sign", false);
    r.set_bool("candidate_models", false);
    r.set_bool("fail_if_inconclusive", true);
    return r;
}

params_ref fallback_params(params_ref const& p) {
    params_ref r = p;
    r.set_bool("arith.nl.linprobe", false);
    r.set_bool("arith.nl.linprobe_mode", false);
    return r;
}

class linprobe_tactic : public tactic {
    tactic_ref m_probe;
    tactic_ref m_fallback;
    params_ref m_params;
    bool m_has_callbacks = false;

public:
    linprobe_tactic(tactic* probe, tactic* fallback, params_ref const& p):
        m_probe(probe),
        m_fallback(fallback),
        m_params(p) {
        updt_params(p);
    }

    char const* name() const override { return "linprobe"; }

    void operator()(goal_ref const& in, goal_ref_buffer& result) override {
        if (!smt_params_helper(m_params).arith_nl_linprobe() || m_has_callbacks) {
            (*m_fallback)(in, result);
            return;
        }

        goal orig(*in);
        try {
            (*m_probe)(in, result);
            return;
        }
        catch (tactic_exception&) {
            result.reset();
            in->reset_all();
            in->copy_from(orig);
        }
        (*m_fallback)(in, result);
    }

    void updt_params(params_ref const& p) override {
        m_params.copy(p);
        m_probe->updt_params(probe_params(p));
        m_fallback->updt_params(fallback_params(p));
    }

    void collect_param_descrs(param_descrs& r) override {
        m_fallback->collect_param_descrs(r);
    }

    void collect_statistics(statistics& st) const override {
        m_probe->collect_statistics(st);
        m_fallback->collect_statistics(st);
    }

    void reset_statistics() override {
        m_probe->reset_statistics();
        m_fallback->reset_statistics();
    }

    void cleanup() override {
        m_probe->cleanup();
        m_fallback->cleanup();
    }

    void reset() override {
        m_probe->reset();
        m_fallback->reset();
    }

    void set_logic(symbol const& l) override {
        m_probe->set_logic(l);
        m_fallback->set_logic(l);
    }

    void set_progress_callback(progress_callback* callback) override {
        m_probe->set_progress_callback(callback);
        m_fallback->set_progress_callback(callback);
    }

    tactic* translate(ast_manager& m) override {
        return alloc(linprobe_tactic, m_probe->translate(m), m_fallback->translate(m), m_params);
    }

    void register_on_clause(void* ctx, user_propagator::on_clause_eh_t& on_clause) override {
        m_has_callbacks = true;
        m_fallback->register_on_clause(ctx, on_clause);
    }

    void user_propagate_init(
        void* ctx,
        user_propagator::push_eh_t& push_eh,
        user_propagator::pop_eh_t& pop_eh,
        user_propagator::fresh_eh_t& fresh_eh) override {
        m_has_callbacks = true;
        m_fallback->user_propagate_init(ctx, push_eh, pop_eh, fresh_eh);
    }

    void user_propagate_register_fixed(user_propagator::fixed_eh_t& fixed_eh) override {
        m_has_callbacks = true;
        m_fallback->user_propagate_register_fixed(fixed_eh);
    }

    void user_propagate_register_final(user_propagator::final_eh_t& final_eh) override {
        m_has_callbacks = true;
        m_fallback->user_propagate_register_final(final_eh);
    }

    void user_propagate_register_eq(user_propagator::eq_eh_t& eq_eh) override {
        m_has_callbacks = true;
        m_fallback->user_propagate_register_eq(eq_eh);
    }

    void user_propagate_register_diseq(user_propagator::eq_eh_t& diseq_eh) override {
        m_has_callbacks = true;
        m_fallback->user_propagate_register_diseq(diseq_eh);
    }

    void user_propagate_register_on_binding(user_propagator::binding_eh_t& binding_eh) override {
        m_has_callbacks = true;
        m_fallback->user_propagate_register_on_binding(binding_eh);
    }

    void user_propagate_register_expr(expr* e) override {
        m_has_callbacks = true;
        m_fallback->user_propagate_register_expr(e);
    }

    void user_propagate_register_created(user_propagator::created_eh_t& created_eh) override {
        m_has_callbacks = true;
        m_fallback->user_propagate_register_created(created_eh);
    }

    void user_propagate_register_decide(user_propagator::decide_eh_t& decide_eh) override {
        m_has_callbacks = true;
        m_fallback->user_propagate_register_decide(decide_eh);
    }

    void user_propagate_clear() override {
        m_has_callbacks = false;
        m_fallback->user_propagate_clear();
    }

    void user_propagate_initialize_value(expr* var, expr* value) override {
        m_has_callbacks = true;
        m_fallback->user_propagate_initialize_value(var, value);
    }
};

tactic* mk_raw_smt_tactic(ast_manager& m, params_ref const& p) {
    sat_params sp(p);
    if (sp.smt())
        return mk_solver2tactic(mk_smt2_solver(m, p));
    if (sp.euf())
        return mk_sat_tactic(m, p);
    return mk_smt_tactic_core(m, p);
}

tactic* mk_linprobe_tactic(ast_manager& m, params_ref const& p) {
    params_ref pp = probe_params(p);
    tactic* probe = try_for(mk_smt_tactic_core(m, pp), linprobe_timeout_ms);
    return alloc(linprobe_tactic, probe, mk_raw_smt_tactic(m, p), p);
}

}

tactic * mk_smt_tactic(ast_manager & m, params_ref const & p) {
    return mk_linprobe_tactic(m, p);
}

tactic * mk_smt_tactic_using(ast_manager& m, bool auto_config, params_ref const& p) {
    params_ref q = p;
    q.set_bool("auto_config", auto_config);
    return using_params(mk_linprobe_tactic(m, q), q);
}
