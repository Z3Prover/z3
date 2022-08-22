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
#include "util/lbool.h"
#include "util/rational.h"
#include "util/vector.h"
#include "util/util.h"


namespace polysat {

    class univariate_solver {
    public:
        using dep_t = unsigned;
        using dep_vector = svector<dep_t>;

        /// Coefficients of univariate polynomial, index == degree,
        /// e.g., the vector [ c, b, a ] represents a*x^2 + b*x + c.
        using univariate = vector<rational>;

        virtual ~univariate_solver() = default;

        virtual void push() = 0;
        virtual void pop(unsigned n) = 0;

        virtual lbool check() = 0;
        virtual dep_vector unsat_core() = 0;
        virtual rational model() = 0;

        virtual void add_ule(univariate const& lhs, univariate const& rhs, bool sign, dep_t dep) = 0;
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

        /// Add x <= val or x > val, depending on sign
        virtual void add_ule_const(rational const& val, bool sign, dep_t dep) = 0;
        /// Add x >= val or x < val, depending on sign
        virtual void add_uge_const(rational const& val, bool sign, dep_t dep) = 0;
        void add_ugt_const(rational const& val, bool sign, dep_t dep) { add_ule_const(val, !sign, dep); }
        void add_ult_const(rational const& val, bool sign, dep_t dep) { add_uge_const(val, !sign, dep); }

        /// Assert i-th bit of x
        virtual void add_bit(unsigned idx, bool sign, dep_t dep) = 0;

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
