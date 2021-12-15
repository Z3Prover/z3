/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    Op constraint.

    lshr: r == p >> q
    ashr: r == p >> q
    lshl: r == p << q
    and:  r == p & q
    or:   r == p | q
    neg:  r == ~p
    xor:  r == p ^ q
    
Author:

    Jakob Rath, Nikolaj Bjorner (nbjorner) 2021-12-09

--*/
#pragma once
#include "math/polysat/constraint.h"

namespace polysat {

    class op_constraint final : public constraint {
    public:
        enum class code { lshr_op, ashr_op, shl_op, and_op, or_op, xor_op, not_op };
    protected:
        friend class constraint_manager;

        code m_op;
        pdd m_p;
        pdd m_q;
        pdd m_r;

        op_constraint(constraint_manager& m, code c, pdd const& p, pdd const& q, pdd const& r);
        void simplify() {}
        bool is_always_false(bool is_positive, pdd const& p, pdd const& q, pdd const& r) const;
        bool is_always_true(bool is_positive, pdd const& p, pdd const& q, pdd const& r) const;
        lbool eval(pdd const& p, pdd const& q, pdd const& r) const;

    public:        
        ~op_constraint() override {}
        pdd const& p() const { return m_p; }
        pdd const& q() const { return m_q; }
        pdd const& r() const { return m_r; }
        std::ostream& display(std::ostream& out, lbool status) const override;
        std::ostream& display(std::ostream& out) const override;
        bool is_always_false(bool is_positive) const override;
        bool is_currently_false(assignment_t const& a, bool is_positive) const override;
        bool is_currently_true(assignment_t const& a, bool is_positive) const override;
        void narrow(solver& s, bool is_positive) override;
        inequality as_inequality(bool is_positive) const override { throw default_exception("is not an inequality"); }
        unsigned hash() const override;
        bool operator==(constraint const& other) const override;
        bool is_eq() const override { return false; }
    };

}
