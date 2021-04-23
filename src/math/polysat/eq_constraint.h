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

    class eq_constraint : public constraint {
        pdd m_poly;
    public:
        eq_constraint(unsigned lvl, pdd const& p, p_dependency_ref& dep):
            constraint(lvl, dep, ckind_t::eq_t), m_poly(p) {
            m_vars.append(p.free_vars());
        }
        ~eq_constraint() override {}
        pdd const & p() const { return m_poly; }
        std::ostream& display(std::ostream& out) const override;
        bool propagate(solver& s, pvar v) override;
        constraint* resolve(solver& s, pvar v) override;
        bool is_always_false() override;
        bool is_currently_false(solver& s) override;
        void narrow(solver& s) override;
    };

}
