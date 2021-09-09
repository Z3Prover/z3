/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    dd_fdd

Abstract:

    Finite domain abstraction for using BDDs as sets of integers, inspired by BuDDy's fdd module.

Author:

    Jakob Rath 2021-04-20
    Nikolaj Bjorner (nbjorner) 2021-04-20

--*/
#pragma once

#include "math/dd/dd_bdd.h"
#include "util/vector.h"
#include "util/rational.h"

namespace dd {

    enum class find_t { empty, singleton, multiple };
    std::ostream& operator<<(std::ostream& out, find_t x);

    /**
     * Finite domain abstraction over BDDs.
     */
    class fdd {
        unsigned_vector m_pos2var;  // pos -> BDD var
        unsigned_vector m_var2pos;  // var -> pos (pos = place number in the bit representation, 0 is LSB's place)
        bdd_manager*    m;
        bddv            m_var;

        static unsigned_vector seq(unsigned count, unsigned start = 0, unsigned step = 1) {
            unsigned_vector result;
            unsigned k = start;
            for (unsigned i = 0; i < count; ++i, k += step)
                result.push_back(k);
            return result;
        }

        unsigned var2pos(unsigned var) const;

        bool contains(bdd const& b, bool_vector const& value) const;

        rational bits2rational(bool_vector const& v) const;

        bool_vector rational2bits(rational const& r) const;

    public:
        /** Initialize FDD using BDD variables from 0 to num_bits-1. */
        fdd(bdd_manager& manager, unsigned num_bits, unsigned start = 0, unsigned step = 1) : fdd(manager, seq(num_bits, start, step)) { }
        fdd(bdd_manager& manager, unsigned_vector const& vars) : fdd(manager, unsigned_vector(vars)) { }
        fdd(bdd_manager& manager, unsigned_vector&& vars);

        unsigned num_bits() const { return m_pos2var.size(); }
        unsigned_vector const& bdd_vars() const { return m_pos2var; }

        bddv const& var() const { return m_var; }

        /** Equivalent to var() != 0 */
        bdd non_zero() const;

        /** Checks whether the integer val is contained in the BDD when viewed as set of integers.
         * Precondition: the bdd only contains variables managed by this fdd.
         */
        bool contains(bdd b, rational const& val) const;

        /** Returns an integer contained in the BDD, if any, and whether the BDD is a singleton.
         * Precondition: the bdd only contains variables managed by this fdd.
         */
        find_t find(bdd b, rational& out_val) const;

        /** Like find, but returns hint if it is contained in the BDD. */
        find_t find_hint(bdd b, rational const& hint, rational& out_val) const;

        /*
         * find largest value at lo or above such that bdd b evaluates to true
         * at lo and all values between.
         * dually, find smallest value below hi that evaluates b to true
         * and all values between the value and hi also evaluate b to true.
         * \param b - a bdd using variables from this
         * \param lo/hi - bound to be traversed.
         * \return false if b is false at lo/hi
         * \pre variables in b are a subset of variables from the fdd
         */
        bool sup(bdd const& b, bool_vector& lo) const;

        bool inf(bdd const& b, bool_vector& hi) const;

        bool sup(bdd const& b, rational& lo) const;

        bool inf(bdd const& b, rational& hi) const;

        /*
        * Find the min-max satisfying assignment.
        * \pre b is not false.
        */
        rational max(bdd b) const;

        rational min(bdd b) const;
    };

}
