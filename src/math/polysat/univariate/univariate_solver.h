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

#include "util/lbool.h"
#include "util/rational.h"
#include "util/vector.h"
#include "util/util.h"


namespace polysat {

    class univariate_solver {
    public:
        using dep_t = unsigned;
        using dep_vector = svector<dep_t>;
        using univariate = vector<rational>;

        virtual ~univariate_solver() = default;

        virtual void push() = 0;
        virtual void pop(unsigned n) = 0;

        virtual lbool check() = 0;
        virtual dep_vector unsat_core() = 0;
        virtual rational model() = 0;

        virtual void add_ule(univariate lhs, univariate rhs, bool sign, dep_t dep) = 0;
        virtual void add_umul_ovfl(univariate lhs, univariate rhs, bool sign, dep_t dep) = 0;
        virtual void add_smul_ovfl(univariate lhs, univariate rhs, bool sign, dep_t dep) = 0;
        virtual void add_smul_udfl(univariate lhs, univariate rhs, bool sign, dep_t dep) = 0;
        // op constraints?
    };

    class univariate_solver_factory {
    public:
        virtual ~univariate_solver_factory();
        virtual scoped_ptr<univariate_solver> operator()() = 0;
    };

    scoped_ptr<univariate_solver_factory> mk_univariate_bitblast_factory();

}
