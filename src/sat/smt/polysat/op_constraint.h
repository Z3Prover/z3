/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    Op constraint.

    lshr: r == p >> q
    ashr: r == p >>a q
    lshl: r == p << q
    and:  r == p & q
    or:   r == p | q

Author:

    Jakob Rath, Nikolaj Bjorner (nbjorner) 2021-12-09

--*/
#pragma once
#include "sat/smt/polysat/constraints.h"
#include <optional>

namespace polysat {

    class core;

    class op_constraint final : public constraint {
    public:
        enum class code {
            /// r is the logical right shift of p by q.
            lshr_op,
            /// r is the arithmetic right shift of p by q.
            ashr_op,
            /// r is the left shift of p by q.
            shl_op,
            /// r is the bit-wise 'and' of p and q.
            and_op,
            /// r is the bit-wise 'or' of p and q.
            or_op,
            /// r is the smallest multiplicative pseudo-inverse of p;
            /// by definition we set r == 0 when p == 0.
            /// Note that in general, there are 2^parity(p) many pseudo-inverses of p.
            inv_op,
        };
    protected:
        friend class constraints;

        code m_op;
        pdd p; // operand1
        pdd q; // operand2
        pdd r; // result
        
        op_constraint(code c, pdd const& r, pdd const& p, pdd const& q);
        lbool eval(pdd const& r, pdd const& p, pdd const& q) const;

        static lbool eval_lshr(pdd const& p, pdd const& q, pdd const& r);
        static lbool eval_ashr(pdd const& p, pdd const& q, pdd const& r);
        static lbool eval_shl(pdd const& p, pdd const& q, pdd const& r);
        static lbool eval_and(pdd const& p, pdd const& q, pdd const& r);
        static lbool eval_inv(pdd const& p, pdd const& r);
        static lbool eval_or(pdd const& p, pdd const& q, pdd const& r);

        bool saturate_lshr(core& c);
        bool saturate_ashr(core& c);
        bool saturate_shl(core& c);
        bool saturate_and(core& c);
        bool saturate_or(core& c);
        bool saturate_inv(core& c);
        bool propagate_mask(core& c, pdd const& p, pdd const& q, pdd const& r, rational const& pv, rational const& qv, rational const& rv);

        bool propagate(core& c, signed_constraint const& sc);
        bool add_conflict(core& c, char const* ax, constraint_or_dependency_list const& cs);

        std::ostream& display(std::ostream& out, char const* eq) const;

    public:
        ~op_constraint() override {}
        code get_op() const { return m_op; }
        std::ostream& display(std::ostream& out, lbool status) const override;
        std::ostream& display(std::ostream& out) const override;
        lbool eval() const override;
        lbool weak_eval(assignment const& a) const override;
        lbool strong_eval(assignment const& a) const override;
        bool is_always_true() const { return false; }
        bool is_always_false() const { return false; }
        void activate(core& c, bool sign, dependency const& dep) override;
        bool saturate(core& c, lbool value, dependency const& dep) override;
    };

}
