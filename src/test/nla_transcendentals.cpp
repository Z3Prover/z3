/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    nla_transcendentals.cpp

Abstract:

    Tests for cross-application transcendental identity axioms. The
    identity pairs (sin/cos, sinh/cosh, cosh/tanh sharing the same
    argument) are no longer tracked on the nla side: nra_solver forwards
    every registered application straight to nlsat, and
    nlsat::transcendentals::add (nlsat/nlsat_transcendentals.cpp) itself
    discovers matching pairs and asserts the corresponding permanent
    polynomial identity. These tests exercise that end-to-end behavior
    through nla::core/nra_solver.

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
    nla_solver.add_transcendental(nlsat::transcendental_op_kind::SIN, t, sin_val);
    nla_solver.add_transcendental(nlsat::transcendental_op_kind::COS, t, cos_val);

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
    nla_solver.add_transcendental(nlsat::transcendental_op_kind::COSH, t, cosh_val);
    nla_solver.add_transcendental(nlsat::transcendental_op_kind::SINH, t, sinh_val);

    s.set_column_value_test(cosh_val, lp::impq(rational(2)));
    s.set_column_value_test(sinh_val, lp::impq(rational(2)));
    s.add_var_bound(cosh_val, lp::lconstraint_kind::LE, rational(2));
    s.add_var_bound(cosh_val, lp::lconstraint_kind::GE, rational(2));
    s.add_var_bound(sinh_val, lp::lconstraint_kind::LE, rational(2));
    s.add_var_bound(sinh_val, lp::lconstraint_kind::GE, rational(2));

    lbool result = nla_solver.test_check();
    VERIFY(result == l_false);
}

// Direct check on core::is_nla_context_satisfied() itself (as opposed to
// test_check(), which additionally goes through the rest of check()'s
// pipeline). Uses a tightly-bounded argument so the plain transcendental
// delta-check (rather than the identity axioms, which additionally require
// bounded_nlsat to actually run) is what catches the bad value: this keeps
// the test independent of nlsat-scheduling timing.
void test_is_nla_context_satisfied() {
    std::cout << "test_is_nla_context_satisfied\n";

    lp::lar_solver s;
    reslimit rl;
    params_ref p;
    p.set_bool("arith.nl.nra", true);

    lpvar x  = s.add_var(0, true);
    lpvar xx = s.add_var(1, true);

    nla::core nla_solver(s, p, rl);
    vector<lpvar> vars;
    vars.push_back(x); vars.push_back(x);
    nla_solver.add_monic(xx, vars.size(), vars.begin());

    s.set_column_value_test(x, lp::impq(rational(3)));
    s.set_column_value_test(xx, lp::impq(rational(9)));

    // Monomial alone is consistent, and there are no transcendentals yet.
    VERIFY(nla_solver.is_nla_context_satisfied());

    lpvar t       = s.add_var(2, true);
    lpvar sin_val = s.add_var(3, true);
    nla_solver.add_transcendental(nlsat::transcendental_op_kind::SIN, t, sin_val);

    // Pin t = 0 tightly, so the delta-check's Taylor sandwich for sin(t)
    // around 0 is tight enough to immediately refute sin_val = 1 (the
    // correct value is 0), without any help from nlsat/identity axioms.
    s.set_column_value_test(t, lp::impq(rational(0)));
    s.add_var_bound(t, lp::lconstraint_kind::LE, rational(0));
    s.add_var_bound(t, lp::lconstraint_kind::GE, rational(0));
    s.set_column_value_test(sin_val, lp::impq(rational(1)));

    // Monomial is still fine, but the context as a whole must be reported
    // unsatisfied because of the bogus sin(t) value.
    VERIFY(!nla_solver.is_nla_context_satisfied());
}

void test_nla_transcendentals() {
    test_sin_cos_identity_detects_conflict();
    test_cosh_sinh_identity_detects_conflict();
    test_is_nla_context_satisfied();
}

} // namespace nla

void tst_nla_transcendentals() {
    nla::test_nla_transcendentals();
}
