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

    class ule_constraint : public constraint {
        pdd m_lhs;
        pdd m_rhs;
    public:
        ule_constraint(unsigned lvl, csign_t sign, pdd const& l, pdd const& r, p_dependency_ref const& dep):
            constraint(lvl, sign, dep, ckind_t::ule_t), m_lhs(l), m_rhs(r) {
            m_vars.append(l.free_vars());
            for (auto v : r.free_vars())
                if (!m_vars.contains(v))
                    m_vars.push_back(v);
        }
        ~ule_constraint() override {}
        pdd const& lhs() const { return m_lhs; }
        pdd const& rhs() const { return m_rhs; }
        std::ostream& display(std::ostream& out) const override;
        constraint* resolve(solver& s, pvar v) override;
        bool is_always_false(pdd const& lhs, pdd const& rhs);
        bool is_always_false() override;
        bool is_currently_false(solver& s) override;
        bool is_currently_true(solver& s) override;
        void narrow(solver& s) override;
        bool forbidden_interval(solver& s, pvar v, eval_interval& out_interval, scoped_ptr<constraint>& out_neg_cond) override;
    };

}
