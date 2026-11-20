/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    sat_activity.cpp

Abstract:

    Test VSIDS activity rescaling in both modes of sat.activity.truncate:
    unsigned activities (the default) zero the activity of a variable
    bumped a few rescales ago, while double
    activities keep the order of variables bumped at different times.
    The parameter is set through params_ref, both at construction and
    through updt_params.

--*/

#include "sat/sat_solver.h"
#include "util/debug.h"
#include "util/rlimit.h"
#include <cmath>

namespace {

    enum class mode { default_params, truncate, no_truncate };

    struct activity_scenario {
        sat::solver& s;
        sat::bool_var hot, older, newer, never;

        activity_scenario(sat::solver& s):
            s(s), hot(s.mk_var()), older(s.mk_var()), newer(s.mk_var()), never(s.mk_var()) {}

        // one "conflict": bump the hot variable, then decay. Returns true
        // if the bump triggered a rescale, the only way the activity of
        // the hot variable goes down.
        bool conflict() {
            double before = s.get_activity(hot);
            s.inc_activity(hot);
            s.decay_activity();
            return s.get_activity(hot) < before;
        }

        // run conflicts until at least min_rescales rescales happened
        void run(unsigned min_rescales) {
            unsigned rescales = 0;
            for (unsigned i = 0; i < 100000 && rescales < min_rescales; ++i)
                rescales += conflict();
            ENSURE(rescales >= min_rescales);
        }

        void bump(sat::bool_var v) {
            s.inc_activity(v);
            s.decay_activity();
        }

        void play() {
            run(1);
            bump(older);
            run(1);
            bump(newer);
            run(1);
        }

        bool is_integer(sat::bool_var v) const {
            double a = s.get_activity(v);
            return a == std::floor(a) && a < 4294967296.0;
        }
    };

    void check_mode(mode m, bool through_updt_params) {
        reslimit limit;
        params_ref p;
        if (m != mode::default_params)
            p.set_bool("activity.truncate", m == mode::truncate);
        params_ref empty;
        sat::solver s(through_updt_params ? empty : p, limit);
        if (through_updt_params)
            s.updt_params(p);
        activity_scenario sc(s);
        sc.play();
        ENSURE(s.get_activity(sc.never) == 0);
        ENSURE(s.get_activity(sc.hot) > s.get_activity(sc.newer));
        if (m == mode::no_truncate) {
            ENSURE(s.get_activity(sc.older) > 0);
            ENSURE(s.get_activity(sc.newer) > s.get_activity(sc.older));
        }
        else {
            // unsigned activities: shifting by 14 bits at
            // every rescale zeroes the variable bumped two rescales ago
            ENSURE(s.get_activity(sc.older) == 0);
            ENSURE(sc.is_integer(sc.hot) && sc.is_integer(sc.newer));
        }
    }

    // after a switch, the solver must still decide every variable: the
    // case-split queue has to hold the unassigned variables
    void check_decides_all(sat::solver& s, activity_scenario& sc) {
        sat::bool_var a = s.mk_var(), b = s.mk_var(), c = s.mk_var(), d = s.mk_var();
        s.mk_clause(sat::literal(a, false), sat::literal(b, false));
        s.mk_clause(sat::literal(a, true), sat::literal(b, false));
        s.mk_clause(sat::literal(c, false), sat::literal(d, false));
        ENSURE(s.check() == l_true);
        for (sat::bool_var v : { sc.hot, sc.older, sc.newer, sc.never, a, b, c, d })
            ENSURE(s.value(v) != l_undef);
    }

    // switching truncation on after a run with doubles brings the
    // activities back into the unsigned range without reordering them
    void check_switch_to_truncate() {
        reslimit limit;
        params_ref p;
        p.set_bool("activity.truncate", false);
        sat::solver s(p, limit);
        activity_scenario sc(s);
        sc.play();
        // grow the activities past the unsigned range (no rescale yet)
        for (unsigned i = 0; i < 500; ++i)
            sc.conflict();
        ENSURE(s.get_activity(sc.hot) > 4294967296.0);
        params_ref q;
        q.set_bool("activity.truncate", true);
        s.updt_params(q);
        ENSURE(sc.is_integer(sc.hot) && sc.is_integer(sc.newer) && sc.is_integer(sc.older));
        ENSURE(s.get_activity(sc.hot) <= (1 << 24));
        ENSURE(s.get_activity(sc.hot) >= s.get_activity(sc.newer));
        ENSURE(s.get_activity(sc.newer) >= s.get_activity(sc.older));
        sc.run(1);
        ENSURE(sc.is_integer(sc.hot));
        check_decides_all(s, sc);
    }

    // switching truncation off keeps the unsigned activities exactly
    void check_switch_to_double() {
        reslimit limit;
        params_ref p;
        sat::solver s(p, limit);
        activity_scenario sc(s);
        sc.run(1);
        sc.bump(sc.newer);
        double hot = s.get_activity(sc.hot), newer = s.get_activity(sc.newer);
        ENSURE(hot > newer && newer > 0);
        params_ref q;
        q.set_bool("activity.truncate", false);
        s.updt_params(q);
        ENSURE(s.get_activity(sc.hot) == hot && s.get_activity(sc.newer) == newer);
        sc.play();
        ENSURE(s.get_activity(sc.older) > 0);
        ENSURE(s.get_activity(sc.newer) > s.get_activity(sc.older));
        check_decides_all(s, sc);
    }

    // copying a solver with double activities into one with unsigned
    // activities keeps their order
    void check_copy_double_to_unsigned() {
        reslimit limit;
        params_ref p;
        p.set_bool("activity.truncate", false);
        sat::solver src(p, limit);
        activity_scenario sc(src);
        sc.play();
        params_ref empty;
        sat::solver dst(empty, limit);
        dst.copy(src);
        ENSURE(dst.num_vars() == src.num_vars());
        for (sat::bool_var v : { sc.hot, sc.older, sc.newer, sc.never })
            ENSURE(dst.get_activity(v) == std::floor(dst.get_activity(v)) && dst.get_activity(v) <= (1 << 24));
        ENSURE(dst.get_activity(sc.hot) > dst.get_activity(sc.newer));
        ENSURE(dst.get_activity(sc.newer) >= dst.get_activity(sc.older));
        ENSURE(dst.get_activity(sc.never) == 0);
    }
}

void tst_sat_activity() {
    for (bool through_updt_params : { false, true }) {
        check_mode(mode::default_params, through_updt_params);
        check_mode(mode::truncate, through_updt_params);
        check_mode(mode::no_truncate, through_updt_params);
    }
    check_switch_to_truncate();
    check_switch_to_double();
    check_copy_double_to_unsigned();
}
