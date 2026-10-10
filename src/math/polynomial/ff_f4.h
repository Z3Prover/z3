/*++
Copyright (c) 2026

Module Name:

    ff_f4.h

Abstract:

    Fixed-width F4 Groebner basis backend and zero-dimensional model
    construction for prime fields.

    The backend is used by ff::engine (ff_polynomial.cpp). It works on
    polynomials in the engine's exchange format and returns:

      - l_true  with a verified assignment, or
      - l_false with the set of input premises used (a conflict core), or
      - l_undef when the ideal is positive-dimensional, the quotient is too
        large, or the field is not supported by a fixed-width representation.

    Soundness contract (identical to the engine's):
      * every derived polynomial is an F_p[x]-combination of inputs whose
        premise indices are included in its dependency set;
      * UNSAT is concluded only from (a) 1 in the ideal, or (b) an exhaustive
        split on all F_p roots of a univariate polynomial q(x) whose membership
        in the ideal has been checked by normal form reduction;
      * SAT is reported only after evaluating every input at the assignment.

    Disequalities f != 0 are encoded with fresh Rabinowitsch variables
    (f * t - 1 = 0), which preserves F_p solutions exactly.

--*/
#pragma once
#include "math/polynomial/ff_polynomial.h"
#include <functional>

namespace ff {

    struct f4_config {
        unsigned max_quotient_dim = 1024;    // largest quotient explored by model construction
        unsigned max_basis = 50000;          // basis elements before giving up
        unsigned max_pairs_per_step = 2048;  // critical pairs per F4 matrix
        unsigned max_depth = 64;             // nested root splits
        unsigned max_vars = 256;             // dense exponent vectors: skip larger systems
        unsigned max_monomials = 4000000;    // interned monomials before giving up
        bool value_split = false;            // enumerate F_p values of a free variable when closure is too large
        unsigned slice_attempts = 0;         // random x_v = r slices per level for positive-dimensional ideals (SAT only)
        unsigned slice_budget = 64;          // total slices per solve
        unsigned max_field_degree = 256;     // adjoin x^p - x for positive-dimensional ideals when p <= this
        unsigned seed = 17;
    };

    struct f4_stats {
        unsigned m_gb_calls = 0, m_matrices = 0, m_rows = 0, m_new_polys = 0;
        unsigned m_zero_reductions = 0, m_splits = 0, m_minpolys = 0, m_roots = 0;
        unsigned m_positive_dim = 0, m_large_quotient = 0, m_unsupported = 0, m_field_closures = 0, m_value_splits = 0, m_slices = 0;
        void collect(statistics &st) const;
    };

    // `charge(k)` is called with a non-negative amount of work; it may throw
    // ff::exhausted to stop the computation.
    lbool f4_solve(rational const &p, std::vector<polynomial> const &eqs, std::vector<polynomial> const &neqs,
                   unsigned num_vars, std::vector<rational> &values, std::set<unsigned> &conflict,
                   f4_config const &cfg, f4_stats &stats, std::function<void(unsigned)> const &charge,
                   std::vector<polynomial> *reduced_basis = nullptr);

    bool f4_supported(rational const &p);
}  // namespace ff
