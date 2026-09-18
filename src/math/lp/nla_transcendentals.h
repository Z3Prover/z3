/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

  nla_transcendentals.h

Author:
  Nikolaj Bjorner (nbjorner)

Description:

  End-game consistency check for transcendental function applications
  (sin, cos, tan, asin, acos, atan, sinh, cosh, tanh, asinh, acosh,
  atanh) registered by theory_lra. These are exactly the transcendental
  operators supported by arith_decl_plugin (OP_SIN .. OP_ATANH); there
  is no OP_EXP/OP_LOG in Z3's arithmetic AST.

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

  Incremental Taylor axioms: each app also remembers the smallest
  number of Maclaurin-series terms (app::taylor_terms) whose sandwich
  nra_solver should assert as a permanent nlsat clause for it (see
  get_taylor and degree_to_exclude). It is seeded to a small default
  degree as soon as the application is registered (so nlsat is never
  handed a completely unconstrained val), and is bumped further, on
  demand, only when check_app finds an actual delta-check failure: the
  degree is chosen to be just large enough that the resulting sandwich
  excludes the specific faulty (arg, val) witness that was observed,
  rather than eagerly asserting a fixed high-degree polynomial for
  every application regardless of whether nlsat's search ever needed
  it. This keeps the polynomial problem nlsat has to solve as small as
  possible while still making progress: a fresh nlsat run only pays
  for the degree that history has shown to be necessary, beyond the
  small default baseline.

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

  - Cross-application identity axioms: when two applications of
    complementary ops share the *same argument variable* (structurally,
    not merely equal in the current model), an exact polynomial
    relation between their two output variables holds for every real
    value of that argument, with no remainder/error term at all (unlike
    the Taylor sandwich, which is only ever an enclosure). These are
    asserted unconditionally and permanently by nra_solver as soon as
    the second application of a matching pair is registered:
      - sin(t), cos(t):   sin(t)^2 + cos(t)^2 = 1
      - sinh(t), cosh(t): cosh(t)^2 - sinh(t)^2 = 1
      - cosh(t), tanh(t): cosh(t)^2 * (1 - tanh(t)^2) = 1
        (derived from tanh = sinh/cosh and the cosh/sinh identity above;
        expressed without needing sinh(t) to be registered at all, and
        safe unconditionally since cosh(t) >= 1 is never 0, unlike e.g.
        cos(t)*tan(t) = sin(t), which would be unsound to assert
        unconditionally since cos(t) can be 0)
    Only the *same lpvar* case is detected (e.g. literally sin(x) and
    cos(x) for the same term x, as internalized); two arguments that
    merely happen to be equal in the current model, or are equal via a
    separately-asserted equality constraint, are not linked this way.

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

  - Wide-box refinement: when a delta-check does fail, check_app first
    tries to build the box-refinement lemma (see above) using arg's
    *actual currently known bounds* in the LP (lar_solver's column
    bounds), rather than a tiny epsilon-sized window around the exact
    current value. Unlike the tiny box, this lemma does not depend on
    the specific value the input happened to take: it is a genuine,
    reusable "(input is within its already-asserted range) => (output
    is within the corresponding function range)" fact, closer in spirit
    to the paper's Algorithm 2 which recomputes boxes from the trail's
    current bounds rather than from an arbitrary point sample. Sound
    range enclosure over such a (possibly wide) box requires accounting
    for critical points of periodic/non-monotonic functions (sin, cos,
    tan, cosh), which wide_interval_eval does in closed form; if the box
    cannot be soundly enclosed this way (e.g. tan has a pole inside it)
    the code falls back to the tiny local box, which by construction
    always exhibits the inconsistency that triggered check_app in the
    first place.

--*/
#pragma once
#include "math/lp/nla_types.h"

namespace nla {

    class core;

    enum class transcendental_op_kind {
        SIN,
        COS,
        TAN,
        ASIN,
        ACOS,
        ATAN,
        SINH,
        COSH,
        TANH,
        ASINH,
        ACOSH,
        ATANH
    };

    class transcendentals {
    public:
        struct app {
            transcendental_op_kind op;
            lpvar                  arg;
            lpvar                  val;
            // Number of Taylor terms whose sandwich axiom nra_solver should
            // assert for this application. Seeded to a small default degree
            // for ops that support it (see k_default_taylor_terms in
            // nla_transcendentals.cpp) as soon as the application is
            // registered, so nlsat always has *some* algebraic connection
            // between arg and val; bumped further (never decreased) by
            // check() only once a delta-check failure exposes an actual
            // inconsistent model, to just enough terms to exclude that
            // specific (arg, val) witness -- see check_app/
            // degree_to_exclude.
            unsigned               taylor_terms = 0;
        };

        // A Maclaurin (Taylor-at-0) polynomial sandwich for a transcendental
        // op: T(x) = sum(coeff * x^power), sound over all reals (not just a
        // local box) via the Lagrange remainder, i.e.
        //   T(x) - remainder_coeff*x^remainder_power <= op(x) <= T(x) + remainder_coeff*x^remainder_power
        // remainder_power is always even (see nla_transcendentals.cpp for the
        // derivation), so the remainder term is manifestly non-negative and
        // no case split on the sign of x is needed. Consumers (nra_solver)
        // use this to inject a permanent polynomial axiom relating val and
        // arg directly into the nlsat problem, giving nlsat's polynomial
        // search an actual algebraic connection between the two instead of
        // treating val as an opaque, unconstrained real.
        struct taylor_term {
            rational coeff;
            unsigned power;
        };
        struct taylor_bounds {
            vector<taylor_term> poly;
            rational            remainder_coeff;
            unsigned            remainder_power;
        };

        // A pair of output variables of two applications with the same
        // (structural) argument, related by an exact polynomial identity
        // (see module comment); consumed by nra_solver to assert the
        // corresponding permanent equality axiom.
        struct identity_pair {
            lpvar v1;
            lpvar v2;
        };

    private:
        core&         m_core;
        vector<app>   m_apps;
        unsigned      m_num_failures = 0;
        // (sin_val, cos_val), (cosh_val, sinh_val), (cosh_val, tanh_val)
        // pairs found so far via matching arguments; see add_transcendental
        // and the module comment for the identities these enable.
        vector<identity_pair> m_sin_cos_pairs;
        vector<identity_pair> m_cosh_sinh_pairs;
        vector<identity_pair> m_cosh_tanh_pairs;
        // The lpvar theory_lra registered for the nullary constant pi, if
        // any (null_lpvar otherwise); see add_pi. Exposed so future checks
        // in this module (and nra_solver) can refer to pi directly, e.g. to
        // express arg-range facts like "0 < arg < pi" symbolically instead
        // of only via pi's already-asserted numeric bound.
        lpvar m_pi_var = null_lpvar;

    public:
        transcendentals(core& c) : m_core(c) {}

        // theory_lra registers (op_kind, input variable, output variable):
        // val is meant to represent op(arg).
        void add_transcendental(transcendental_op_kind op, lpvar arg, lpvar val);

        // theory_lra registers the lpvar it created for the nullary
        // constant pi. Unlike add_transcendental, there is no argument and
        // no delta-check/Taylor-sandwich machinery applies (pi is not the
        // output of a function of some other variable); this just asserts
        // pi's permanent tight-rational range axiom (see add_range_axioms)
        // and remembers the lpvar so other checks in this module can refer
        // to pi directly. A no-op if val is null or pi has already been
        // registered.
        void add_pi(lpvar val);

        // null_lpvar if theory_lra has not (yet) registered pi.
        lpvar pi_var() const { return m_pi_var; }

        bool empty() const { return m_apps.empty(); }

        vector<app> const& apps() const { return m_apps; }

        // Cross-application identity pairs discovered so far (see the
        // identity_pair doc comment and the module-level comment on
        // cross-application identity axioms); consumed by nra_solver to
        // assert sin(t)^2+cos(t)^2=1, cosh(t)^2-sinh(t)^2=1, and
        // cosh(t)^2*(1-tanh(t)^2)=1 respectively.
        vector<identity_pair> const& sin_cos_pairs() const { return m_sin_cos_pairs; }
        vector<identity_pair> const& cosh_sinh_pairs() const { return m_cosh_sinh_pairs; }
        vector<identity_pair> const& cosh_tanh_pairs() const { return m_cosh_tanh_pairs; }

        // fills out a Taylor sandwich using num_terms terms of the Maclaurin
        // series for op; returns false if none is available yet (currently
        // implemented for SIN and COS only) or if num_terms == 0.
        static bool get_taylor(transcendental_op_kind op, unsigned num_terms, taylor_bounds& out);

        // delta-check every registered application against the current
        // assignment; asserts a box-refinement lemma via lemma_builder
        // when an application is found inconsistent.
        void check();

        // Certify (or refute) an nra (nlsat) model as an acceptable model
        // for all registered transcendental applications, using the
        // Taylor-sandwich remainder at each application's *actual* nlsat
        // witness (read via core::nra_model_bound, not the stale plain-LP
        // core::val). Requires use_nra_model() and a Taylor sandwich to be
        // available for every registered op; returns false (reject) rather
        // than trying to be clever when either is missing, since there is
        // then no certificate that val is a good enough approximation of
        // op(arg). This is what allows bounded_nlsat()'s l_true, obtained
        // using the (sound but possibly very loose, for large |arg|) Taylor
        // sandwich axioms, to be trusted as an actual model.
        bool check_nra_model();

        // true once at least one application has an accumulated Taylor
        // axiom (see app::taylor_terms); used to gate bounded_nlsat calls
        // that would otherwise be pointless (no axiom yet means nlsat has
        // no more information about any val than "free real").
        bool has_axioms() const {
            for (auto const& a : m_apps)
                if (a.taylor_terms > 0)
                    return true;
            return false;
        }

        // true once check_app has actually observed a delta-check failure
        // (as opposed to every application merely carrying its seeded
        // default-degree axiom from registration). Unlike has_axioms, this
        // does not trip on the very first, typically-trivial round where
        // the current assignment already passes the plain delta-check:
        // handing that problem to nlsat too would only add cost (and risk)
        // for no expected benefit, since the reactive delta-check alone
        // was already about to succeed.
        bool has_observed_failure() const { return m_num_failures > 0; }

    private:
        bool check_app(app& a);
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
        static bool has_linear_majorant(transcendental_op_kind op);
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
        // Smallest number of Taylor terms (1..max_terms) such that the
        // (floating point estimate of the) resulting sandwich at x
        // provably excludes y, i.e. would contradict the faulty model
        // (x, y) if asserted; 0 if no such degree is found within
        // max_terms (x too large / y too close to op(x) for this
        // approach to help).
        static unsigned degree_to_exclude(transcendental_op_kind op, double x, double y, unsigned max_terms = 30);
        static double eval(transcendental_op_kind op, double x);
        static double error_bound(transcendental_op_kind op, double x, double fx);
        static char const* op_name(transcendental_op_kind op);
        // enclosure [lo_val, hi_val] of op over the (intentionally tiny) box
        // [lo, hi], inflated by error_bound at the box endpoints/center;
        // sound as long as op does not stray far from monotonic between lo
        // and hi (true for a small enough box, but not in general).
        static void interval_eval(transcendental_op_kind op, double lo, double hi, double& lo_val, double& hi_val);
        // A sound enclosure [lo_val, hi_val] of op over a (possibly wide)
        // box [lo, hi], accounting in closed form for op's critical points
        // (sin/cos maxima/minima, cosh's minimum at 0) so it remains valid
        // regardless of box width. Returns false when no sound enclosure by
        // this method is available (tan has a pole inside [lo, hi]); the
        // caller should fall back to interval_eval on a tiny box instead.
        static bool wide_interval_eval(transcendental_op_kind op, double lo, double hi, double& lo_val, double& hi_val);
        // exact rational equal to the (finite) double d.
        static rational to_rational(double d);
        // asserts permanent, unconditional column bounds on val that hold
        // for every application of op (see the module comment).
        void add_range_axioms(transcendental_op_kind op, lpvar val);
    };
}
