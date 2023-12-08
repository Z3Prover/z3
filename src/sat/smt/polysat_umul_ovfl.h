/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat multiplication overflow constraint

Author:

    Jakob Rath, Nikolaj Bjorner (nbjorner) 2021-12-09

--*/
#pragma once
#include "sat/smt/polysat_constraints.h"

namespace polysat {

    class umul_ovfl_constraint final : public constraint {

        pdd m_p;
        pdd m_q;

        void simplify();
        static bool is_always_true(bool is_positive, pdd const& p, pdd const& q) { return eval(p, q) == to_lbool(is_positive); }
        static bool is_always_false(bool is_positive, pdd const& p, pdd const& q) { return is_always_true(!is_positive, p, q); }
        static lbool eval(pdd const& p, pdd const& q);

    public:
        umul_ovfl_constraint(pdd const& p, pdd const& q);
        ~umul_ovfl_constraint() override {}
        pdd const& p() const { return m_p; }
        pdd const& q() const { return m_q; }
        std::ostream& display(std::ostream& out, lbool status) const override;
        std::ostream& display(std::ostream& out) const override;
        lbool eval() const override;
        lbool eval(assignment const& a) const override;
    };

}
