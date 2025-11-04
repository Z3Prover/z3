
/*++
  Copyright (c) 2025 Microsoft Corporation

  Module Name:

  nla_bounds.cpp

  Author:
    Lev Nachmanson (levnach)
    Nikolaj Bjorner (nbjorner)

--*/

#include "nla_bounds.h"
#include "nla_core.h"


namespace nla {

    bounds::bounds(core *c) : common(c) {}

    // looking for a free variable inside of a monic to split
    void bounds::operator()() {
        for (lpvar i : c().to_refine()) {
            auto const &m = c().emons()[i];
            for (lpvar j : m.vars()) {
                if (add_bounds_to_free_variable(m, j) ||
                    add_bounds_to_variable_at_value(j, 0) ||
                    add_bounds_to_variable_at_value(j, 1) ||
                    add_bounds_to_variable_at_value(j, -1)) {
                    ++c().lp_settings().stats().m_nla_add_bounds;
                    return;
                }
            }
        }
    }

    bool bounds::add_bounds_to_free_variable(monic const& m, lp::lpvar j) {
        if (!c().var_is_free(j))
            return false;
        if (m.is_bound_propagated())
            return false;
        c().emons().set_bound_propagated(m);
        // split the free variable (j <= 0, or j > 0), and return
        auto i(ineq(j, lp::lconstraint_kind::LE, rational::zero()));
        c().add_literal(i);
        TRACE(nla_solver, c().print_ineq(i, tout) << "\n");
        return true;
    }

    bool bounds::add_bounds_to_variable_at_value(lp::lpvar j, int value) {
        // disable new functionality
        // return false;
        auto v = c().val(j);
        if (v != value)
            return false;
        if (c().var_is_fixed(j))
            return false;
        u_dependency *d = nullptr;
        lp::mpq bound;
        bool is_strict;
        if (c().has_lower_bound(j, d, bound, is_strict) && (bound > value || (bound == value && is_strict)))
            return false;
        if (c().has_upper_bound(j, d, bound, is_strict) && (bound < value || (bound == value && is_strict)))
            return false;
        // fix a bound that hasn't already been fixed.
        if (c().has_lower_bound(j) && c().get_lower_bound(j) == value) {
            auto i(ineq(j, lp::lconstraint_kind::LE, rational(value)));
            TRACE(nla_solver, c().print_ineq(i, tout) << "\n");
            c().add_literal(i);
        } 
        else {
            auto i(ineq(j, lp::lconstraint_kind::GE, rational(value)));
            TRACE(nla_solver, c().print_ineq(i, tout) << "\n");
            c().add_literal(i);
        }
        IF_VERBOSE(2, verbose_stream() << "unit bound j" << j << " = " << value << "\n");
        return true;
    }

}  // namespace nla
