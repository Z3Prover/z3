/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    nla_transcendentals.cpp

Abstract:

    Tests for cross-application transcendental identity axioms
    (nla::transcendentals::sin_cos_pairs/cosh_sinh_pairs/cosh_tanh_pairs,
    consumed by nra_solver::add_identity_axioms) in math/lp.

Author:

    Test Coverage Improvement

Revision History:

--*/

#include "math/lp/nla_core.h"
#include "math/lp/lar_solver.h"
#include "util/rational.h"
#include "util/rlimit.h"

namespace nla {

// sin(t)^2 + cos(t)^2 = 1 should catch an assignment that is monomial-wise
// consistent (each square is within its trivial [0,1] range) but violates
// the Pythagorean identity, only once the identity axiom is actually
// injected into nlsat. test_check() (level 2) is used because it reaches
// the unconditional nra_solver::check() call in nla_core::check(), unlike
// the throttled/backoff-gated bounded_nlsat() used at lower levels.
void test_sin_cos_identity_detects_conflict() {
    std::cout << "test_sin_cos_identity_detects_conflict\n";

    lp::lar_solver s;
    reslimit rl;
    params_ref p;
    p.set_bool("arith.nl.nra", true);

    lpvar t       = s.add_var(0, true);
    lpvar sin_val = s.add_var(1, true);
    lpvar cos_val = s.add_var(2, true);
    lpvar sin2    = s.add_var(3, true);
    lpvar cos2    = s.add_var(4, true);

    nla::core nla_solver(s, p, rl);
    nla_solver.add_transcendental(nla::transcendental_op_kind::SIN, t, sin_val);
    nla_solver.add_transcendental(nla::transcendental_op_kind::COS, t, cos_val);

    vector<lpvar> sin_vars, cos_vars;
    sin_vars.push_back(sin_val); sin_vars.push_back(sin_val);
    cos_vars.push_back(cos_val); cos_vars.push_back(cos_val);
    nla_solver.add_monic(sin2, sin_vars.size(), sin_vars.begin());
    nla_solver.add_monic(cos2, cos_vars.size(), cos_vars.begin());

    // sin_val = cos_val = 0.8: each square is 0.64, individually within the
    // (already-known, identity-independent) [0,1] range, but their sum
    // (1.28) contradicts sin^2+cos^2=1.
    s.set_column_value_test(sin_val, lp::impq(rational(4), rational(5)));
    s.set_column_value_test(cos_val, lp::impq(rational(4), rational(5)));
    s.set_column_value_test(sin2, lp::impq(rational(16), rational(25)));
    s.set_column_value_test(cos2, lp::impq(rational(16), rational(25)));
    s.add_var_bound(sin2, lp::lconstraint_kind::GE, rational(3, 5));
    s.add_var_bound(cos2, lp::lconstraint_kind::GE, rational(3, 5));

    lbool result = nla_solver.test_check();
    VERIFY(result == l_false);
}

// cosh(t)^2 - sinh(t)^2 = 1: pick cosh_val = sinh_val = 2 (consistent with
// cosh(t) >= 1 individually, but violating the hyperbolic identity, which
// forces cosh^2 - sinh^2 = 1 rather than 0).
void test_cosh_sinh_identity_detects_conflict() {
    std::cout << "test_cosh_sinh_identity_detects_conflict\n";

    lp::lar_solver s;
    reslimit rl;
    params_ref p;
    p.set_bool("arith.nl.nra", true);

    lpvar t        = s.add_var(0, true);
    lpvar cosh_val = s.add_var(1, true);
    lpvar sinh_val = s.add_var(2, true);

    nla::core nla_solver(s, p, rl);
    nla_solver.add_transcendental(nla::transcendental_op_kind::COSH, t, cosh_val);
    nla_solver.add_transcendental(nla::transcendental_op_kind::SINH, t, sinh_val);

    s.set_column_value_test(cosh_val, lp::impq(rational(2)));
    s.set_column_value_test(sinh_val, lp::impq(rational(2)));
    s.add_var_bound(cosh_val, lp::lconstraint_kind::LE, rational(2));
    s.add_var_bound(cosh_val, lp::lconstraint_kind::GE, rational(2));
    s.add_var_bound(sinh_val, lp::lconstraint_kind::LE, rational(2));
    s.add_var_bound(sinh_val, lp::lconstraint_kind::GE, rational(2));

    lbool result = nla_solver.test_check();
    VERIFY(result == l_false);
}

void test_nla_transcendentals() {
    test_sin_cos_identity_detects_conflict();
    test_cosh_sinh_identity_detects_conflict();
}

} // namespace nla

void tst_nla_transcendentals() {
    nla::test_nla_transcendentals();
}
