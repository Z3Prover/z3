/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat multiplication overflow constraint

Author:

    Jakob Rath, Nikolaj Bjorner (nbjorner) 2021-12-09

--*/
#pragma once
#include "sat/smt/polysat/constraints.h"

namespace polysat {

    class umul_ovfl_constraint final : public constraint {

        pdd m_p;
        pdd m_q;

        void simplify();
        static bool is_always_true(bool is_positive, pdd const& p, pdd const& q) { return eval(p, q) == to_lbool(is_positive); }
        static bool is_always_false(bool is_positive, pdd const& p, pdd const& q) { return is_always_true(!is_positive, p, q); }
        static lbool eval(pdd const& p, pdd const& q);

        bool narrow_bound(core& c, bool is_positive, pdd const& p0, pdd const& q0, pdd const& p, pdd const& q, dependency const& d);

    public:
        umul_ovfl_constraint(pdd const& p, pdd const& q);
        ~umul_ovfl_constraint() override {}
        pdd const& p() const { return m_p; }
        pdd const& q() const { return m_q; }
        std::ostream& display(std::ostream& out, lbool status) const override;
        std::ostream& display(std::ostream& out) const override;
        lbool eval() const override;
        lbool eval(assignment const& a) const override;
        void activate(core& c, bool sign, dependency const& dep) override;
        void propagate(core& c, lbool value, dependency const& dep) override;
    };


    class umul_ovfl {
        constraint_id m_id;
        signed_constraint sc;
    public:
        umul_ovfl(constraint_id id, signed_constraint sc) : m_id(id), sc(sc) {}
        pdd p() const { return sc.to_umul_ovfl().p(); }
        pdd q() const { return sc.to_umul_ovfl().q(); }
        bool sign() const { return sc.sign(); }
        constraint_id id() const { return m_id; }
    };

}
