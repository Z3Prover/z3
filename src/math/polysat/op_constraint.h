/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    Op constraint.

    lshr: r == p >> q
    ashr: r == p >>a q
    lshl: r == p << q
    and:  r == p & q
    or:   r == p | q
    not:  r == ~p
    xor:  r == p ^ q
    
Author:

    Jakob Rath, Nikolaj Bjorner (nbjorner) 2021-12-09

--*/
#pragma once
#include "math/polysat/constraint.h"

namespace polysat {

    class solver;

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

        void narrow_lshr(solver& s);
        lbool eval_lshr(pdd const& p, pdd const& q, pdd const& r) const;

        void narrow_and(solver& s);
        lbool eval_and(pdd const& p, pdd const& q, pdd const& r) const;

    public:        
        ~op_constraint() override {}
        pdd const& p() const { return m_p; }
        pdd const& q() const { return m_q; }
        pdd const& r() const { return m_r; }
        std::ostream& display(std::ostream& out, lbool status) const override;
        std::ostream& display(std::ostream& out) const override;
        bool is_always_false(bool is_positive) const override;
        bool is_currently_false(solver& s, bool is_positive) const override;
        bool is_currently_true(solver& s, bool is_positive) const override;
        bool is_currently_false(solver& s, assignment_t const& sub, bool is_positive) const override { return false; }
        bool is_currently_true(solver& s, assignment_t const& sub, bool is_positive) const override { return false; }
        void narrow(solver& s, bool is_positive, bool first) override;
        inequality as_inequality(bool is_positive) const override { throw default_exception("is not an inequality"); }
        unsigned hash() const override;
        bool operator==(constraint const& other) const override;
        bool is_eq() const override { return false; }

        void add_to_univariate_solver(solver& s, univariate_solver& us, unsigned dep, bool is_positive) const override;
    };

}
