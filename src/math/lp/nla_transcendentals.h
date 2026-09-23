/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

  nla_transcendentals.h

Author:
  Nikolaj Bjorner (nbjorner)

Description:

  End-game consistency check for transcendental function applications
  (sin, cos, tan, asin, acos, atan, sinh, cosh, tanh, asinh, acosh,
  atanh, exp, atan2, log) registered by theory_lra.

  nlsat/nra_solver reason about polynomial arithmetic over algebraic
  numbers and have no representation for transcendental functions, so
  the nla_core search never gets any feedback connecting an "input"
  variable to an "output" variable that is meant to track a
  transcendental function applied to it. Currently these operators are
  treated as underspecified/uninterpreted by the arith theory solver
  (see arith_internalize.cpp) or purified away (purify_arith_tactic.cpp)
  rather than consumed here; this module is the nla_core-side consumer
  that such front-end wiring would eventually feed.

  This module implements a cheap, best-effort delta-satisfiability
  check in the sense of Gallego-Hernandez, Lipparini, Mansutti, "MCSAT
  Modulo Transcendental Arithmetics" (arXiv:2606.00697): given the
  current numeric assignment to the input/output variables of a
  registered application, it evaluates the transcendental function in
  floating point, inflates the result by a conservative error bound to
  account for floating point round-off, and checks whether the output
  value is within a delta-tolerance of the (inflated) function value.

  - If it is, the application is treated as consistent and is not an
    obstacle to reporting the current assignment as a model.
  - If it is not, the check derives a genuine conflict lemma rather
    than a plain case split, following the shape of the "TRA
    refinement" step of the paper (their Algorithm 2, also
    implemented in the Yices-TRA prototype's
    src/mcsat/na/na_plugin_explain.c): it brackets the current value
    of the input variable in a small rational box [lo,hi], computes a
    (floating point, safety-inflated) enclosure [flo,fhi] of op over
    that box, and asserts the implication
        (arg < lo \/ arg > hi \/ flo <= val <= fhi)
    as a lemma via lemma_builder. This is a real conflict clause (all
    disjuncts are false in the current model, since arg is inside the
    box while val is outside its image), so unlike a case split it
    directly refines the NRA abstraction and can be reused/subsumed
    like any other nla lemma, instead of merely nudging the search.
    The box is intentionally tiny (governed by
    arith.nl.transcendental_tolerance) so that the endpoint-sampling
    used to compute [flo,fhi] stays close to monotonic between lo and
    hi; this is an engineering approximation, not a certified interval
    enclosure (Yices-TRA uses arbitrary-precision interval arithmetic
    via the ARB library for that).

  This check is unsound-incomplete "on purpose": it never returns
  l_false, and accepting an assignment as consistent within delta does
  not certify that an exact model exists. It is meant to be a fast
  filter that runs before the (nonexistent, for transcendentals) exact
  decision procedure.

  Note on the split of responsibilities with nlsat: this module used
  to also derive its own reactive Taylor-sandwich/box-refinement
  polynomial lemmas whenever the delta-check above failed (bracketing
  arg in a small box, sampling op in floating point over that box, and
  asserting the resulting enclosure as a conflict clause). That
  machinery has been removed: it was floating point-driven and could
  nudge the LP assignment indefinitely without ever producing a
  certificate, and it duplicated exact, terminating refinement that
  nlsat now performs itself (see nlsat/nlsat_transcendentals.h/.cpp,
  in particular its Taylor/Maclaurin brackets for exp/log/atan/sin/cos).
  Instead, a delta-check failure here is only recorded
  (has_observed_failure); core::check_transcendentals_and_finish uses
  that, together with should_run_bounded_nlsat()'s backoff scheduler,
  to hand the problem to nra_solver/nlsat, whose own
  nlsat::transcendentals engine refines the polynomial constraints
  relating arg and val internally. This module therefore only ever
  contributes *linear* facts to the LP relaxation (range axioms,
  global linear-majorant/monotonicity/sign lemmas below), while every
  polynomial constraint on a transcendental application is owned by
  nlsat.

  Two additional, stronger propagation mechanisms are layered on top of
  the per-application delta-check above:

  - Range axioms: mathematically exact (or, where pi is involved,
    outward-rounded so as to remain exact) global bounds on the output
    variable are asserted once, permanently, as soon as an application
    is registered (e.g. -1 <= sin(t), cos(t) <= 1; -1 < tanh(t) < 1;
    cosh(t) >= 1; 0 <= acos(t) <= pi; -pi/2 <= asin(t) <= pi/2; -pi/2 <
    atan(t) < pi/2; acosh(t) >= 0). These are true unconditionally, so
    unlike the lemmas below they are added directly as column bounds
    (lar_solver::add_var_bound) rather than as conflict clauses, and
    immediately prune the search space rather than waiting for an
    inconsistent sample to be found first.

  - Cross-application identity axioms (sin(t)^2+cos(t)^2=1,
    cosh(t)^2-sinh(t)^2=1, cosh(t)^2*(1-tanh(t)^2)=1, for two
    applications of complementary ops sharing the *same argument
    variable*) are no longer tracked or asserted here: nra_solver
    forwards every registered application straight to nlsat (see
    register_transcendentals_with_nlsat), and
    nlsat::transcendentals::add (nlsat/nlsat_transcendentals.cpp) already
    discovers matching pairs and asserts the identical permanent
    polynomial equality itself the moment the second application of a
    pair reaches it - duplicating that bookkeeping on this side only
    grew this module without adding any coverage nlsat did not already
    provide.

  - Global linear-majorant lemmas: sin, tanh, and atan all satisfy
    op(0) = 0 and are 1-Lipschitz, so none of them can cross the line
    y = x: op(t) <= t for every t >= 0, and op(t) >= t for every t <= 0.
    Unlike range axioms, this relates val to arg (not a single column
    to a constant) and unlike a permanent bound it need not always
    hold trivially against the current box, so it is asserted as an
    actual (exact, tolerance-free) two-literal lemma via lemma_builder
    - e.g. (arg < 0 \/ val <= arg) - rather than as a column bound.
    check_app tries this check (check_linear_majorant) *before* the
    floating point delta-check/box-refinement lemma above, since it is
    exact and, when it applies, strictly stronger evidence than a
    locally-sampled enclosure.

  - Sign-on-range lemmas: once pi is registered (see add_pi/pi_var), sin
    and cos each satisfy an exact sign fact on a pi-relative range that
    the floating point delta-check above cannot express as a *global*,
    tolerance-free fact: sin(t) > 0 for 0 < t < pi and sin(t) < 0 for
    -pi < t < 0; cos(t) > 0 for -pi/2 < t < pi/2 and cos(t) < 0 for pi/2
    < t < 3pi/2 (the latter expressed via the doubled argument 2t vs
    +/-pi, so no separate pi/2 variable is needed). Like the linear
    majorant above this is asserted as an exact two-or-three-literal
    lemma via lemma_builder - e.g. (arg <= 0 \/ arg >= pi \/ val > 0) -
    referencing pi_var() symbolically rather than only its numeric
    bound, and is tried with the same priority as the linear majorant,
    before the floating point delta-check.

--*/
#pragma once
#include "math/lp/nla_types.h"
#include "nlsat/nlsat_transcendentals.h"

namespace nla {

    class core;

    class transcendentals {
    public:
        struct app {
            nlsat::transcendental_op_kind op;
            lpvar                  arg;
            lpvar                  val;
        };

        // A registered application of the binary function atan2(y, x),
        // val meant to represent atan2(y, x) (the 2-argument arctangent,
        // range (-pi, pi]). This is a genuinely different shape from app
        // above (two input variables, playing structurally different
        // roles - y's sign alone fixes val's sign, x's sign alone selects
        // the branch), so it is kept as a separate, self-contained
        // registration/check path rather than shoehorned into the
        // single-argument nlsat::transcendental_op_kind family; see add_atan2 and
        // check_atan2 in nla_transcendentals.cpp.
        struct atan2_app {
            lpvar y;
            lpvar x;
            lpvar val;
        };

    private:
        core&         m_core;
        vector<app>   m_apps;
        unsigned      m_num_failures = 0;
        // The lpvar theory_lra registered for the nullary constant pi, if
        // any (null_lpvar otherwise); see add_pi. Exposed so future checks
        // in this module (and nra_solver) can refer to pi directly, e.g. to
        // express arg-range facts like "0 < arg < pi" symbolically instead
        // of only via pi's already-asserted numeric bound.
        lpvar m_pi_var = null_lpvar;

        // Registered atan2(y, x) applications; see atan2_app and add_atan2.
        vector<atan2_app> m_atan2_apps;

    public:
        transcendentals(core& c) : m_core(c) {}

        // theory_lra registers (op_kind, input variable, output variable):
        // val is meant to represent op(arg).
        void add_transcendental(nlsat::transcendental_op_kind op, lpvar arg, lpvar val);

        // theory_lra registers the lpvar it created for the nullary
        // constant pi. Unlike add_transcendental, there is no argument and
        // no delta-check/Taylor-sandwich machinery applies (pi is not the
        // output of a function of some other variable); this just asserts
        // pi's permanent tight-rational range axiom (see add_range_axioms)
        // and remembers the lpvar so other checks in this module can refer
        // to pi directly. A no-op if val is null or pi has already been
        // registered.
        void add_pi(lpvar val);

        // theory_lra registers a binary atan2(y, x) application: y and x
        // are the two input variables, val the output. Asserts atan2's
        // permanent range axiom (-pi <= val <= pi) and records the
        // application for check() (see check_atan2). A no-op if any of y,
        // x, val is null.
        void add_atan2(lpvar y, lpvar x, lpvar val);

        // null_lpvar if theory_lra has not (yet) registered pi.
        lpvar pi_var() const { return m_pi_var; }

        bool empty() const { return m_apps.empty() && m_atan2_apps.empty(); }

        vector<app> const& apps() const { return m_apps; }
        vector<atan2_app> const& atan2_apps() const { return m_atan2_apps; }

        // delta-check every registered application against the current
        // assignment; asserts a lemma via lemma_builder for exact,
        // tolerance-free facts (linear majorant/monotonicity/sign/range),
        // and records has_observed_failure for a plain delta-check
        // failure - see the module comment.
        void check();

        // Sanity-checks nra_solver's (nlsat's) own model against the plain
        // delta-tolerance used by check_app, using each application's
        // *actual* nlsat witness (read via core::nra_model_bound, not the
        // stale plain-LP core::val). See the module comment for why this
        // is expected to always pass.
        bool check_nra_model();

        // true once check_app has actually observed a delta-check failure.
        // Used to gate bounded_nlsat calls that would otherwise be
        // pointless: handing the problem to nlsat too early (before any
        // failure) would only add cost for no expected benefit, since the
        // reactive delta-check alone was already about to succeed.
        bool has_observed_failure() const { return m_num_failures > 0; }

    private:
        bool check_app(app& a);
        // atan2(y, x): the exact fact sign(val) == sign(y) whenever y != 0
        // (val and y share a sign regardless of x's sign or magnitude -
        // atan2's quadrant selection never flips the sign of the result
        // relative to y), asserted as a lemma when violated; then a
        // float-based delta-check against std::atan2(y, x) with a coarse
        // case-split on sign(x) as fallback (rather than full 2D box
        // refinement - atan2's branch structure makes a tight closed-form
        // box enclosure substantially more involved, and is out of scope
        // here; see the module comment).
        bool check_atan2(atan2_app& a);
        // True for op such that op(0) = 0 and op is 1-Lipschitz (sin,
        // tanh, atan): each then satisfies the *exact*, global (not just
        // locally-around-the-current-point) fact op(x) <= x for x >= 0 and
        // op(x) >= x for x <= 0, since op cannot cross the line y = x
        // without its slope exceeding 1 somewhere. Unlike the reactive
        // Taylor-sandwich box-refinement lemma (whose reach and tightness
        // depend on floating point evaluation and an accumulated degree),
        // this is exact rational arithmetic and holds unconditionally, so
        // check_app tries it with priority, before falling back to the
        // Taylor sandwich.
        static bool has_linear_majorant(nlsat::transcendental_op_kind op);
        // Checks the fact from has_linear_majorant against the current
        // assignment and, on violation, asserts it as a two-literal lemma
        // (arg's sign disjunct, or val <= arg / val >= arg) - a global
        // inequality *lemma* relating val to arg, in contrast to the
        // permanent single-column constant *bounds* added once in
        // add_range_axioms. Returns true iff a lemma was asserted.
        bool check_linear_majorant(app& a);
        // For SIN: exact fact that sin > 0 on (0, pi) and sin < 0 on
        // (-pi, 0) (derived symbolically from pi_var, not from pi's
        // numeric bound, so it stays exact even though pi_var's own bound
        // is only an outward-rounded rational approximation of pi). For
        // COS: the analogous fact that cos > 0 on (-pi/2, pi/2) and cos <
        // 0 on (pi/2, 3pi/2), expressed via the doubled argument (2*arg
        // vs +/-pi) so no separate pi/2 variable is needed. A no-op
        // (returns false) if pi has not been registered (pi_var() ==
        // null_lpvar) or a.op is neither SIN nor COS.
        bool check_sign_on_pi_range(app& a);
        // EXP: the exact, tolerance-free, global inequality exp(t) >= 1+t
        // for every real t (equivalently, T_1's Maclaurin lower bound at
        // degree 1, sound unconditionally - unlike sin/cos/tan/etc.,
        // exp is not entire-with-bounded-derivatives, so the general
        // get_taylor sandwich machinery does not apply to it; see the
        // module comment and nla_transcendentals.cpp for the TOCL/MathSAT
        // paper's derivation of this and the other exp-specific facts
        // below). Asserted as a single-literal lemma (no case split
        // needed, since it holds for every t) whenever violated.
        bool check_exp_lower_bound(app& a);
        // EXP: monotonicity - exp(x1) < exp(x2) whenever x1 < x2. Checked
        // pairwise across all registered EXP applications (the paper's
        // "Monotonicity constraint"); asserted as a two-literal lemma
        // whenever two applications currently violate it.
        bool check_exp_monotonicity(app& a);
        // LOG: the exact, tolerance-free, global inequality log(x) <= x-1
        // for every x > 0 (tangent line at x=1; log is concave, so every
        // tangent line is a global upper bound over its domain - the dual
        // of check_exp_lower_bound's exp(t) >= 1+t, via the substitution
        // t = log(x)). Guarded by a disjunct on arg's sign (unlike
        // check_exp_lower_bound, log's domain is x > 0, not all reals), so
        // this is a two-literal (not single-literal) lemma when violated.
        bool check_log_upper_bound(app& a);
        // LOG: monotonicity - log(x1) < log(x2) whenever 0 < x1 < x2.
        // Checked pairwise across all registered LOG applications with a
        // positive argument (mirrors check_exp_monotonicity); a no-op for
        // any pairing where either argument is non-positive (out of log's
        // domain, not this check's responsibility).
        bool check_log_monotonicity(app& a);
        static double eval(nlsat::transcendental_op_kind op, double x);
        static double error_bound(nlsat::transcendental_op_kind op, double x, double fx);
        static char const* op_name(nlsat::transcendental_op_kind op);
        // exact rational equal to the (finite) double d.
        static rational to_rational(double d);
        // asserts permanent, unconditional column bounds on val that hold
        // for every application of op (see the module comment).
        void add_range_axioms(nlsat::transcendental_op_kind op, lpvar val);
    };
}
