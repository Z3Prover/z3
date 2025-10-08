/*++
  Copyright (c) 2025

  Module Name:

  nlsat_common.h

  Abstract:

  Pretty-print helpers for NLSAT components as free functions.
  These forward to existing solver/pmanager display facilities.

  --*/
#pragma once

#include "nlsat/nlsat_assignment.h"
#include "nlsat/nlsat_solver.h"
#include "nlsat/nlsat_scoped_literal_vector.h"
#include "math/polynomial/polynomial_cache.h"

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

    inline std::ostream& display(std::ostream& out, solver& s, poly* p) {
        return display(out, s.pm(), polynomial_ref(p, s.pm()), s.display_proc());
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

    /**
     * \brief Display a vector of algebraic numbers in several commonly useful formats.
     *
     * This mirrors the ad-hoc helper that existed in `src/test/algebraic.cpp` so that
     * solver / explanation code can conveniently dump root sets while debugging.
     *
     * For each algebraic number it prints (in order):
     *  - a decimal approximation (10 digits)
     *  - the root object representation (defining polynomial & isolating interval)
     *  - the isolating interval alone
     *
     */
    inline void display(std::ostream & out, scoped_anum_vector const & rs) {
        algebraic_numbers::manager & m = rs.m();
        out << "numbers in decimal:\n";
        for (const auto & r : rs) {
            m.display_decimal(out, r, 10);
            out << '\n';
        }
        out << "numbers as root objects\n";
        for (const auto & r : rs) {
            m.display_root(out, r);
            out << '\n';
        }
        out << "numbers as intervals\n";
        for (const auto & r : rs) {
            m.display_interval(out, r);
            out << '\n';
        }
    }
        /**
           \brief Wrapper for factorization
        */
    void factor(polynomial_ref & p, polynomial::cache& cache, polynomial_ref_vector & fs);

} // namespace nlsat
