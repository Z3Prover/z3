/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    Op constraint.

    lshr: r == p >> q
    ashr: r == p >>a q
    lshl: r == p << q
    and:  r == p & q
    not:  r == ~p

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

        void propagate_lshr(core& s, dependency const& dep);
        void propagate_ashr(core& s, dependency const& dep);
        void propagate_shl(core& s, dependency const& dep);
        void propagate_and(core& s, dependency const& dep);
        void propagate_inv(core& s, dependency const& dep);

        

        std::ostream& display(std::ostream& out, char const* eq) const;

        void activate_and(core& s, dependency const& d);
        void activate_ashr(core& s, dependency const& d);

    public:
        ~op_constraint() override {}
        code get_op() const { return m_op; }
        std::ostream& display(std::ostream& out, lbool status) const override;
        std::ostream& display(std::ostream& out) const override;
        lbool eval() const override;
        lbool eval(assignment const& a) const override;
        bool is_always_true() const { return false; }
        bool is_always_false() const { return false; }
        void activate(core& c, bool sign, dependency const& dep) override;
        void propagate(core& c, lbool value, dependency const& dep) override;
    };

}
