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
#include <optional>

namespace polysat {

    class solver;

    class op_constraint final : public constraint {
    public:
        enum class code { lshr_op, ashr_op, shl_op, and_op, or_op, xor_op };
    protected:
        friend class constraint_manager;

        code m_op;
        pdd m_p;
        pdd m_q;
        pdd m_r;

        op_constraint(constraint_manager& m, code c, pdd const& p, pdd const& q, pdd const& r);
        lbool eval(pdd const& p, pdd const& q, pdd const& r) const;

        void narrow_lshr(solver& s);
        static lbool eval_lshr(pdd const& p, pdd const& q, pdd const& r);

        void narrow_shl(solver& s);
        static lbool eval_shl(pdd const& p, pdd const& q, pdd const& r);

        void narrow_and(solver& s);
        static lbool eval_and(pdd const& p, pdd const& q, pdd const& r);

        std::ostream& display(std::ostream& out, char const* eq) const;

    public:
        ~op_constraint() override {}
        pdd const& p() const { return m_p; }
        pdd const& q() const { return m_q; }
        pdd const& r() const { return m_r; }
        std::ostream& display(std::ostream& out, lbool status) const override;
        std::ostream& display(std::ostream& out) const override;
        lbool eval() const override;
        lbool eval(assignment const& a) const override;
        void narrow(solver& s, bool is_positive, bool first) override;
        unsigned hash() const override;
        bool operator==(constraint const& other) const override;
        bool is_eq() const override { return false; }

        void add_to_univariate_solver(solver& s, univariate_solver& us, unsigned dep, bool is_positive) const override;
    };

    struct op_constraint_args {
        op_constraint::code op;
        // NOTE: this is only optional because table2map requires a default constructor
        std::optional<std::pair<pdd, pdd>> args;

        op_constraint_args() = default;
        op_constraint_args(op_constraint::code op, pdd lhs, pdd rhs)
            : op(op), args({std::move(lhs), std::move(rhs)}) {}

        bool operator==(op_constraint_args const& other) const {
            return op == other.op && args == other.args;
        }

        unsigned hash() const {
            unsigned const lhs_hash = args ? args->first.hash() : 0;
            unsigned const rhs_hash = args ? args->second.hash() : 0;
            return mk_mix(static_cast<unsigned>(op), lhs_hash, rhs_hash);
        }
    };

}
