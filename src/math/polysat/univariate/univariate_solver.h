/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    polysat abstract univariate solver

Abstract:

    Solver interface for univariate polynomials over modular arithmetic.

Author:

    Nikolaj Bjorner (nbjorner) 2022-03-10
    Jakob Rath 2022-03-10

--*/
#pragma once

#include <ostream>
#include "ast/ast.h"
#include "util/lbool.h"

namespace polysat {

    class univariate_solver {
    protected:
        unsigned bit_width;
    public:
        using dep_t = unsigned;
        using dep_vector = svector<dep_t>;

        /// Coefficients of univariate polynomial, index == degree,
        /// e.g., the vector [ c, b, a ] represents a*x^2 + b*x + c.
        using univariate = vector<rational>;

        const dep_t null_dep = UINT_MAX;

        univariate_solver(unsigned bit_width) : bit_width(bit_width) {}

        virtual ~univariate_solver() = default;

        virtual void push() = 0;
        virtual void pop(unsigned n) = 0;
        virtual unsigned scope_level() const = 0;

        virtual lbool check() = 0;

        /**
         * Precondition: check() returned l_false
         */
        dep_vector unsat_core();
        virtual void unsat_core(dep_vector& out_deps) = 0;

        /**
         * Precondition: check() returned l_true
         */
        virtual rational model() = 0;

        /**
         * Find minimal model.
         *
         * Precondition: check() returned l_true
         * Returns: true on success, false on resource out.
         */
        bool find_min(rational& out_min);

        /**
         * Find maximal model.
         *
         * Precondition: check() returned l_true
         * Returns: true on success, false on resource out.
         */
        bool find_max(rational& out_max);

        /**
         * Find up to two viable values.
         *
         * Precondition: check() returned l_true
         * returns: true on success, false on resource out
         */
        virtual bool find_two(rational& out1, rational& out2) = 0;

        /** lhs <= rhs */
        virtual void add_ule(univariate const& lhs, univariate const& rhs, bool sign, dep_t dep) = 0;
        virtual void add_ule(univariate const& lhs, rational   const& rhs, bool sign, dep_t dep) = 0;
        virtual void add_ule(rational   const& lhs, univariate const& rhs, bool sign, dep_t dep) = 0;
        /** lhs >= rhs */
        void add_uge(univariate const& lhs, univariate const& rhs, bool sign, dep_t dep) { add_ule(rhs, lhs, sign, dep); }
        void add_uge(univariate const& lhs, rational   const& rhs, bool sign, dep_t dep) { add_ule(rhs, lhs, sign, dep); }
        void add_uge(rational   const& lhs, univariate const& rhs, bool sign, dep_t dep) { add_ule(rhs, lhs, sign, dep); }
        /** lhs < rhs */
        void add_ult(univariate const& lhs, univariate const& rhs, bool sign, dep_t dep) { add_ule(rhs, lhs, !sign, dep); }
        void add_ult(univariate const& lhs, rational   const& rhs, bool sign, dep_t dep) { add_ule(rhs, lhs, !sign, dep); }
        void add_ult(rational   const& lhs, univariate const& rhs, bool sign, dep_t dep) { add_ule(rhs, lhs, !sign, dep); }
        /** lhs > rhs */
        void add_ugt(univariate const& lhs, univariate const& rhs, bool sign, dep_t dep) { add_ule(lhs, rhs, !sign, dep); }
        void add_ugt(univariate const& lhs, rational   const& rhs, bool sign, dep_t dep) { add_ule(lhs, rhs, !sign, dep); }
        void add_ugt(rational   const& lhs, univariate const& rhs, bool sign, dep_t dep) { add_ule(lhs, rhs, !sign, dep); }

        virtual void add_umul_ovfl(univariate const& lhs, univariate const& rhs, bool sign, dep_t dep) = 0;
        virtual void add_smul_ovfl(univariate const& lhs, univariate const& rhs, bool sign, dep_t dep) = 0;
        virtual void add_smul_udfl(univariate const& lhs, univariate const& rhs, bool sign, dep_t dep) = 0;
        virtual void add_lshr(univariate const& in1, univariate const& in2, univariate const& out, bool sign, dep_t dep) = 0;
        virtual void add_ashr(univariate const& in1, univariate const& in2, univariate const& out, bool sign, dep_t dep) = 0;
        virtual void add_shl(univariate const& in1, univariate const& in2, univariate const& out, bool sign, dep_t dep) = 0;
        virtual void add_and(univariate const& in1, univariate const& in2, univariate const& out, bool sign, dep_t dep) = 0;
        virtual void add_or(univariate const& in1, univariate const& in2, univariate const& out, bool sign, dep_t dep) = 0;
        virtual void add_xor(univariate const& in1, univariate const& in2, univariate const& out, bool sign, dep_t dep) = 0;
        virtual void add_not(univariate const& in, univariate const& out, bool sign, dep_t dep) = 0;
        virtual void add_inv(univariate const& in, univariate const& out, bool sign, dep_t dep) = 0;
        virtual void add_udiv(univariate const& in1, univariate const& in2, univariate const& out, bool sign, dep_t dep) = 0;
        virtual void add_urem(univariate const& in1, univariate const& in2, univariate const& out, bool sign, dep_t dep) = 0;

        /// Add x <= val or x > val, depending on sign
        virtual void add_ule_const(rational const& val, bool sign, dep_t dep) = 0;
        /// Add x >= val or x < val, depending on sign
        virtual void add_uge_const(rational const& val, bool sign, dep_t dep) = 0;
        void add_ugt_const(rational const& val, bool sign, dep_t dep) { add_ule_const(val, !sign, dep); }
        void add_ult_const(rational const& val, bool sign, dep_t dep) { add_uge_const(val, !sign, dep); }

        /// Assert i-th bit of x
        virtual void add_bit(unsigned idx, bool sign, dep_t dep) = 0;
        void add_bit0(unsigned idx, dep_t dep) { add_bit(idx, true, dep); }
        void add_bit1(unsigned idx, dep_t dep) { add_bit(idx, false, dep); }

        virtual std::ostream& display(std::ostream& out) const = 0;
    };

    inline std::ostream& operator<<(std::ostream& out, univariate_solver& s) {
        return s.display(out);
    }

    class univariate_solver_factory {
    public:
        virtual ~univariate_solver_factory() = default;
        virtual scoped_ptr<univariate_solver> operator()(unsigned bit_width) = 0;
    };

    scoped_ptr<univariate_solver_factory> mk_univariate_bitblast_factory();

}
