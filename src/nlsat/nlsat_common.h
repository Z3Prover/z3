/*++
  Copyright (c) 2025

  Module Name:

  nlsat_common.h

  Abstract:

  Pretty-print helpers for NLSAT components as free functions.
  These forward to existing solver/pmanager display facilities.

  --*/
#pragma once

#include "nlsat/nlsat_solver.h"
#include "nlsat/nlsat_scoped_literal_vector.h"
namespace nlsat {

    inline std::ostream& display(std::ostream& out, pmanager& pm, polynomial_ref const& p, display_var_proc const& proc) {
        pm.display(out, p, proc);
        return out;
    }

    inline std::ostream& display(std::ostream& out, pmanager& pm, polynomial_ref_vector const& ps, display_var_proc const& proc, char const* delim = "\n") {
        for (unsigned i = 0; i < ps.size(); ++i) {
            if (i > 0) out << delim;
            pm.display(out, ps.get(i), proc);
        }
        return out;
    }

    inline std::ostream& display(std::ostream& out, solver& s, polynomial_ref const& p) {
        return display(out, s.pm(), p, s.display_proc());
    }

    inline std::ostream& display(std::ostream& out, solver& s, polynomial_ref_vector const& ps, char const* delim = "\n") {
        return display(out, s.pm(), ps, s.display_proc(), delim);
    }

    inline std::ostream& display(std::ostream& out, solver& s, literal l) {
        return s.display(out, l);
    }

    inline std::ostream& display(std::ostream& out, solver& s, unsigned n, literal const* ls) {
        return s.display(out, n, ls);
    }

    inline std::ostream& display(std::ostream& out, solver& s, literal_vector const& ls) {
        return s.display(out, ls);
    }

    inline std::ostream& display(std::ostream& out, solver& s, scoped_literal_vector const& ls) {
        return s.display(out, ls.size(), ls.data());
    }

    inline std::ostream& display_var(std::ostream& out, solver& s, var x) {
        return s.display(out, x);
    }
    /**
       \brief evaluate the given polynomial in the current interpretation.
       max_var(p) must be assigned in the current interpretation.
    */
    inline ::sign sign(polynomial_ref const & p, assignment & x2v, anum_manager& am) {
        SASSERT(max_var(p) == null_var || x2v.is_assigned(max_var(p)));
        auto s = am.eval_sign_at(p, x2v);
        return s;
    }

    /**
     * Check whether all coefficients of the polynomial `s` (viewed as a polynomial
     * in its main variable) evaluate to zero under the given assignment `x2v`.
     * This is exactly the logic used in several places in the nlsat codebase
     * (e.g. coeffs_are_zeroes_in_factor in nlsat_explain.cpp).
     */
    inline bool coeffs_are_zeroes_on_sample(polynomial_ref const & s, pmanager & pm, assignment & x2v, anum_manager & am) {
        polynomial_ref c(pm);
        var x = pm.max_var(s);
        unsigned n = pm.degree(s, x);
        for (unsigned j = 0; j <= n; ++j) {
            c = pm.coeff(s, x, j);
            if (sign(c, x2v, am) != 0)
                return false;
        }
        return true;
    }

} // namespace nlsat
