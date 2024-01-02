/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat unsigned <= constraint

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-06

--*/
#pragma once
#include "sat/smt/polysat/assignment.h"
#include "sat/smt/polysat/constraints.h"


namespace polysat {

    class ule_constraint final : public constraint {
        pdd m_lhs, m_rhs;
        unsigned_vector m_unfold_vars;
        pdd m_unfold_lhs, m_unfold_rhs;        
        static bool is_always_true(bool is_positive, pdd const& lhs, pdd const& rhs) { return eval(lhs, rhs) == to_lbool(is_positive); }
        static bool is_always_false(bool is_positive, pdd const& lhs, pdd const& rhs) { return is_always_true(!is_positive, lhs, rhs); }
        static lbool eval(pdd const& lhs, pdd const& rhs);

    public:
        ule_constraint(pdd const& l, pdd const& r, pdd const& ul, pdd const& ur);
        ~ule_constraint() override {}
        pdd const& lhs() const { return m_lhs; }
        pdd const& rhs() const { return m_rhs; }
        pdd const& unfold_lhs() const { return m_unfold_lhs; }
        pdd const& unfold_rhs() const { return m_unfold_rhs; }
        static std::ostream& display(std::ostream& out, lbool status, pdd const& lhs, pdd const& rhs);
        unsigned_vector const& unfold_vars() const override { return m_unfold_vars; }
        std::ostream& display(std::ostream& out, lbool status) const override;
        std::ostream& display(std::ostream& out) const override;
        lbool eval() const override;
        lbool eval(assignment const& a) const override;
        lbool eval_unfold(assignment const& a) const override;
        bool is_linear() const override { return lhs().is_linear_or_value() && rhs().is_linear_or_value(); }
        void activate(core& c, bool sign, dependency const& dep);
        void propagate(core& c, lbool value, dependency const& dep) {}
        bool is_eq() const { return m_rhs.is_zero(); }
        unsigned power_of_2() const { return m_lhs.power_of_2(); }

        static void simplify(bool& is_positive, pdd& lhs, pdd& rhs);
        static bool is_simplified(pdd const& lhs, pdd const& rhs);  // return true if lhs <= rhs is not simplified further. this is meant to be used in assertions.
    };

    struct ule_pp {
        lbool status;
        pdd lhs;
        pdd rhs;
        ule_pp(lbool status, pdd const& lhs, pdd const& rhs): status(status), lhs(lhs), rhs(rhs) {}
        ule_pp(lbool status, ule_constraint const& ule): status(status), lhs(ule.lhs()), rhs(ule.rhs()) {}
    };

    inline std::ostream& operator<<(std::ostream& out, ule_pp const& u) { return ule_constraint::display(out, u.status, u.lhs, u.rhs); }

}
