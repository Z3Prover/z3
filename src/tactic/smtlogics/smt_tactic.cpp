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

/**
   \brief Parameters for the monomial linearization probe.

   Only cheap, deterministic nonlinear propagation is enabled, and the probe is
   asked to fail (rather than report unknown) so that the full solver is used as
   a fallback.
*/
params_ref probe_params(params_ref const& p) {
    params_ref r = p;
    r.set_bool("auto_config", false);
    r.set_bool("parallel.enable", false);
    r.set_uint("arith.solver", 6);
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

tactic* mk_raw_smt_tactic(ast_manager& m, params_ref const& p) {
    sat_params sp(p);
    if (sp.smt())
        return mk_solver2tactic(mk_smt2_solver(m, p));
    if (sp.euf())
        return mk_sat_tactic(m, p);
    return mk_smt_tactic_core(m, p);
}

/**
   \brief Run a short monomial linearization probe before \c fallback.

   \c fallback is only reached when the probe fails to close the goal, and it is
   the only branch that supports user propagation.
*/
tactic* mk_linprobe_tactic(ast_manager& m, params_ref const& p, tactic* fallback) {
    params_ref pp = probe_params(p);
    unsigned timeout = smt_params_helper(pp).arith_nl_linprobe_timeout();
    tactic* probe = using_params(try_for(mk_smt_tactic_core(m, pp), timeout), pp);
    return or_else_no_user_propagate(probe, fallback, p, [](params_ref const& q) {
        return smt_params_helper(q).arith_nl_linprobe();
    });
}

}

tactic * mk_smt_tactic(ast_manager & m, params_ref const & p) {
    params_ref fp = fallback_params(p);
    return mk_linprobe_tactic(m, p, using_params(mk_raw_smt_tactic(m, fp), fp));
}

tactic * mk_smt_tactic_using(ast_manager& m, bool auto_config, params_ref const& p) {
    params_ref q = p;
    q.set_bool("auto_config", auto_config);
    params_ref fp = fallback_params(q);
    sat_params sp(fp);
    tactic* fallback = sp.euf() ? mk_sat_tactic(m, fp) : mk_smt_tactic_core_using(m, auto_config, fp);
    return mk_linprobe_tactic(m, q, using_params(fallback, fp));
}
