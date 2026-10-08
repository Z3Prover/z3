/*++
Copyright (c) 2026 Microsoft Corporation

Numerical ordering of arithmetic model values.
--*/
#pragma once

#include "ast/arith_decl_plugin.h"
#include "math/polynomial/algebraic_numbers.h"
#include "util/index_sort_with_mutations.h"

class arith_value_order {
    arith_util const& a;
public:
    explicit arith_value_order(arith_util const& a) : a(a) {}

    bool is_supported(expr* x) const {
        return a.is_numeral(x) || a.is_irrational_algebraic_numeral(x);
    }

    bool operator()(expr* x, expr* y) const {
        SASSERT(is_supported(x) && is_supported(y));
        if (x == y)
            return false;
        rational vx, vy;
        bool rx = a.is_numeral(x, vx);
        bool ry = a.is_numeral(y, vy);
        if (rx && ry)
            return vx < vy;
        if (rx)
            return a.am().gt(a.to_irrational_algebraic_numeral(y), vx.to_mpq());
        if (ry)
            return a.am().lt(a.to_irrational_algebraic_numeral(x), vy.to_mpq());
        return a.am().lt(a.to_irrational_algebraic_numeral(x), a.to_irrational_algebraic_numeral(y));
    }

    // Return false, leaving values unchanged, if an exact ordering is unavailable.
    bool sort(unsigned n, expr** values) const {
        for (unsigned i = 0; i < n; ++i)
            if (!is_supported(values[i]))
                return false;
        if (n < 2)
            return true;
        unsigned_vector perm, scratch;
        for (unsigned i = 0; i < n; ++i)
            perm.push_back(i);
        scratch.resize(n);
        // Algebraic comparisons can refine intervals and consume resources.
        // Keep the comparison sequence independent of the standard library.
        stable_index_merge_sort(perm.data(), scratch.data(), n,
                                [&](unsigned i, unsigned j) { return (*this)(values[i], values[j]); });
        ptr_buffer<expr> sorted;
        for (unsigned i : perm)
            sorted.push_back(values[i]);
        std::copy(sorted.begin(), sorted.end(), values);
        return true;
    }
};
