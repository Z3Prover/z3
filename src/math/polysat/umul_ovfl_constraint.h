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

    class umul_ovfl_constraint final : public constraint {
        friend class constraint_manager;

        pdd m_p;
        pdd m_q;

        umul_ovfl_constraint(constraint_manager& m, pdd const& p, pdd const& q);
        void simplify();
        static bool is_always_true(bool is_positive, pdd const& p, pdd const& q) { return eval(p, q) == to_lbool(is_positive); }
        static bool is_always_false(bool is_positive, pdd const& p, pdd const& q) { return is_always_true(!is_positive, p, q); }
        static lbool eval(pdd const& p, pdd const& q);
        bool narrow_bound(solver& s, bool is_positive, pdd const& p0, pdd const& q0, pdd const& p, pdd const& q);
        bool try_viable(solver& s, bool is_positive, pdd const& p0, pdd const& q0, pdd const& p, pdd const& q);

    public:
        ~umul_ovfl_constraint() override {}
        pdd const& p() const { return m_p; }
        pdd const& q() const { return m_q; }
        std::ostream& display(std::ostream& out, lbool status) const override;
        std::ostream& display(std::ostream& out) const override;
        lbool eval() const override;
        lbool eval(assignment const& a) const override;
        void narrow(solver& s, bool is_positive, bool first) override;

        inequality as_inequality(bool is_positive) const override { throw default_exception("is not an inequality"); }
        unsigned hash() const override;
        bool operator==(constraint const& other) const override;
        bool is_eq() const override { return false; }

        void add_to_univariate_solver(solver& s, univariate_solver& us, unsigned dep, bool is_positive) const override;
    };

}
