/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat multiplication overflow constraint

Author:

    Jakob Rath, Nikolaj Bjorner (nbjorner) 2021-12-09

--*/
#pragma once
#include "math/polysat/constraint.h"

namespace polysat {

    class solver;

    class smul_ovfl_constraint final : public constraint {
        friend class constraint_manager;

        bool m_is_overflow;
        pdd  m_p;
        pdd  m_q;

        void simplify();
        smul_ovfl_constraint(constraint_manager& m, pdd const& p, pdd const& q, bool is_overflow);
        
    public:
        ~smul_ovfl_constraint() override {}
        pdd const& p() const { return m_p; }
        pdd const& q() const { return m_q; }
        std::ostream& display(std::ostream& out, lbool status) const override;
        std::ostream& display(std::ostream& out) const override;
        bool is_always_false(bool is_positive) const override { return false; }
        void narrow(solver& s, bool is_positive, bool first) override;
        bool is_currently_false(solver & s, bool is_positive) const override { return false; }
        bool is_currently_true(solver& s, bool is_positive) const override { return false; }
        bool is_currently_false(solver& s, assignment_t const& sub, bool is_positive) const override { return false; }
        bool is_currently_true(solver& s, assignment_t const& sub, bool is_positive) const override { return false; }

        inequality as_inequality(bool is_positive) const override { throw default_exception("is not an inequality"); }
        unsigned hash() const override;
        bool operator==(constraint const& other) const override;
        bool is_eq() const override { return false; }
    };

}
