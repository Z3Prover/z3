/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat equality constraints

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

--*/
#pragma once
#include "math/polysat/constraint.h"


namespace polysat {

    class eq_constraint final : public constraint {
        friend class constraint_manager;

        pdd m_poly;

        eq_constraint(constraint_manager& m, pdd const& p):
            constraint(m, ckind_t::eq_t), m_poly(p) {
            m_vars.append(p.free_vars());
        }

    public:
        ~eq_constraint() override {}
        pdd const & p() const { return m_poly; }
        std::ostream& display(std::ostream& out, lbool status) const override;
        bool is_always_false(bool is_positive) const override;
        bool is_currently_false(solver& s, bool is_positive) const override;
        bool is_currently_true(solver& s, bool is_positive) const override;
        void narrow(solver& s, bool is_positive) override;
        inequality as_inequality(bool is_positive) const override;
        unsigned hash() const override;
        bool operator==(constraint const& other) const override;
    };

}
