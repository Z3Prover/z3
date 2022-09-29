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
        static void simplify(bool& is_positive, pdd& lhs, pdd& rhs);
        static bool is_always_false(bool is_positive, pdd const& lhs, pdd const& rhs);

    public:
        ~ule_constraint() override {}
        pdd const& lhs() const { return m_lhs; }
        pdd const& rhs() const { return m_rhs; }
        static std::ostream& display(std::ostream& out, lbool status, pdd const& lhs, pdd const& rhs);
        std::ostream& display(std::ostream& out, lbool status) const override;
        std::ostream& display(std::ostream& out) const override;
        bool is_always_false(bool is_positive) const override;
        bool is_currently_false(solver& s, bool is_positive) const override;
        bool is_currently_false(solver& s, assignment_t const& sub, bool is_positive) const override;
        void narrow(solver& s, bool is_positive, bool first) override;
        inequality as_inequality(bool is_positive) const override;
        unsigned hash() const override;
        bool operator==(constraint const& other) const override;
        bool is_eq() const override { return m_rhs.is_zero(); }
        void add_to_univariate_solver(solver& s, univariate_solver& us, unsigned dep, bool is_positive) const override;
    };

    struct ule_pp {
        lbool status;
        pdd lhs;
        pdd rhs;
        ule_pp(lbool status, pdd const& lhs, pdd const& rhs): status(status), lhs(lhs), rhs(rhs) {}
    };

    inline std::ostream& operator<<(std::ostream& out, ule_pp const& u) { return ule_constraint::display(out, u.status, u.lhs, u.rhs); }

}
