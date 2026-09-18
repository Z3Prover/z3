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

        struct app {
            transcendental_op_kind op;
            lpvar                  arg;
            lpvar                  val;
        };

        core&         m_core;
        vector<app>   m_apps;

    public:
        transcendentals(core& c) : m_core(c) {}

        // theory_lra registers (op_kind, input variable, output variable):
        // val is meant to represent op(arg).
        void add_transcendental(transcendental_op_kind op, lpvar arg, lpvar val);

        bool empty() const { return m_apps.empty(); }

        // delta-check every registered application against the current
        // assignment; asserts a box-refinement lemma via lemma_builder
        // when an application is found inconsistent.
        void check();

    private:
        bool check_app(app const& a);
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
