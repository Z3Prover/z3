/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat unsigned <= constraint

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

--*/
#pragma once
#include "math/polysat/constraint.h"


namespace polysat {

    class solver;

    class ule_constraint final : public constraint {
        friend class constraint_manager;

        pdd m_lhs;
        pdd m_rhs;

        ule_constraint(constraint_manager& m, pdd const& l, pdd const& r);
        void simplify();

    public:
        ~ule_constraint() override {}
        pdd const& lhs() const { return m_lhs; }
        pdd const& rhs() const { return m_rhs; }
        std::ostream& display(std::ostream& out, lbool status) const override;
        std::ostream& display(std::ostream& out) const override;
        bool is_always_false(bool is_positive, pdd const& lhs, pdd const& rhs) const;
        bool is_always_false(bool is_positive) const override;
        bool is_currently_false(solver& s, bool is_positive) const override;
        bool is_currently_true(solver& s, bool is_positive) const override;
        bool is_currently_false(solver& s, assignment_t const& sub, bool is_positive) const override;
        bool is_currently_true(solver& s, assignment_t const& sub, bool is_positive) const override;
        void narrow(solver& s, bool is_positive) override;
        inequality as_inequality(bool is_positive) const override;
        unsigned hash() const override;
        bool operator==(constraint const& other) const override;
        bool is_eq() const override { return m_rhs.is_zero(); }
        bool is_diseq() const override { return m_lhs.is_one(); }
        // pdd const& p() const { SASSERT(is_eq()); return m_lhs; }
    };

}
