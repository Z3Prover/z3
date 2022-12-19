/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat multiplication overflow constraint

Author:

    Jakob Rath, Nikolaj Bjorner (nbjorner) 2021-12-09

--*/
#include "math/polysat/smul_fl_constraint.h"
#include "math/polysat/solver.h"

namespace polysat {

    smul_fl_constraint::smul_fl_constraint(constraint_manager& m, pdd const& p, pdd const& q, bool is_overflow):
        constraint(m, ckind_t::smul_fl_t), m_is_overflow(is_overflow), m_p(p), m_q(q) {
        simplify();
        m_vars.append(m_p.free_vars());
        for (auto v : m_q.free_vars())
            if (!m_vars.contains(v))
                m_vars.push_back(v);

    }
    void smul_fl_constraint::simplify() {
        if (m_p.is_zero() || m_q.is_zero() ||
            m_p.is_one() || m_q.is_one()) {
            m_q = 0;
            m_p = 0;
            return;
        }
        if (m_p.index() > m_q.index())
            std::swap(m_p, m_q);
    }

    std::ostream& smul_fl_constraint::display(std::ostream& out, lbool status) const {
        switch (status) {
        case l_true: return display(out);
        case l_false: return display(out << "~");
        case l_undef: return display(out << "?");
        }
        return out;
    }

    std::ostream& smul_fl_constraint::display(std::ostream& out) const {
        if (m_is_overflow)
            return out << "sovfl*(" << m_p << ", " << m_q << ")";
        else
            return out << "sudfl*(" << m_p << ", " << m_q << ")";
    }

    /**
     * TODO - verify the rules for small bit-widths.
     *
     *  sovfl(p,q) => p >= 2, q >= 2
     *  sovfl(p,q) => p >s 0 <=> q >s 0
     *  sovfl(p,q) & p >s 0 => p*q < 0 or ovfl(p,q)
     *  sovfl(p,q) & p <s 0 => p*q < 0 or ovfl(-p,-q)

     * ~sovfl(p,q) & p >s 0 = q >s 0 =>  q > 0 => ~ovfl(p,q) & p*q >=s 0
     * smul_noovfl(p,q) => sign(p) != sign(q) or p'*q' < 2^{K-1}

     * sudfl(p, q) => p >= 2, q >= 2
     * sudfl(p, q) => p >s 0 xor q >s 0
     * sudfl(p, q) & p >s 0 => p*q > 0 or ovfl(p, -q)
     * sudfl(p, q) & q >s 0 => p*q > 0 or ovfl(-p, q)
     *
     * ~sudfl(p, q) & p >s 0 & q <s 0 => ~ovfl(p, -q) & p*q <s 0
     * ~sudfl(p, q) & p <s 0 & q >s 0 => ~ovfl(-p, q) & p*q <s 0
     */
    void smul_fl_constraint::narrow(solver& s, bool is_positive, bool first) {
        if (!first)
            return;
        signed_constraint sc(this, is_positive);
        if (m_is_overflow) {
            if (is_positive) {
                s.add_clause(~sc, s.ule(2, p()), false);
                s.add_clause(~sc, s.ule(2, q()), false);
                s.add_clause(~sc, ~s.sgt(p(), 0), s.sgt(q(), 0), false);
                s.add_clause(~sc, ~s.sgt(q(), 0), s.sgt(p(), 0), false);
                s.add_clause(~sc, ~s.sgt(p(), 0), s.slt(p()*q(), 0), s.umul_ovfl(p(), q()), false);
                s.add_clause(~sc, s.sgt(p(), 0),  s.slt(p()*q(), 0), s.umul_ovfl(-p(), -q()), false);
            }
            else {
                s.add_clause(~sc, ~s.sgt(p(), 0), ~s.sgt(q(), 0), ~s.umul_ovfl(p(), q()), false);
                s.add_clause(~sc, ~s.sgt(p(), 0), ~s.sgt(q(), 0), ~s.slt(p()*q(), 0), false);
                s.add_clause(~sc, ~s.slt(p(), 0), ~s.slt(q(), 0), ~s.umul_ovfl(-p(), -q()), false);
                s.add_clause(~sc, ~s.slt(p(), 0), ~s.slt(q(), 0), ~s.slt((-p())*(-q()), 0), false);
            }
        }
        else {
            if (is_positive) {
                s.add_clause(~sc, s.ule(2, p()), false);
                s.add_clause(~sc, s.ule(2, q()), false);
                s.add_clause(~sc, ~s.sgt(p(), 0), ~s.sgt(q(), 0), false);
                s.add_clause(~sc, s.sgt(q(), 0), s.sgt(p(), 0), false);
                s.add_clause(~sc, ~s.sgt(p(), 0), s.sgt(p()*q(), 0), s.umul_ovfl(p(), -q()), false);
                s.add_clause(~sc, ~s.sgt(q(), 0), s.sgt(p()*q(), 0), s.umul_ovfl(-p(), q()), false);
            }
            else {
                s.add_clause(sc, ~s.sgt(p(), 0), ~s.slt(q(), 0), s.umul_ovfl(p(), -q()), false);
                s.add_clause(sc, ~s.sgt(p(), 0), ~s.slt(q(), 0), s.slt(p()*q(), 0), false);
                s.add_clause(sc, ~s.slt(p(), 0), ~s.sgt(q(), 0), s.umul_ovfl(-p(), q()), false);
                s.add_clause(sc, ~s.slt(p(), 0), ~s.sgt(q(), 0), s.slt(p()*q(), 0), false);
            }
        }
    }

    unsigned smul_fl_constraint::hash() const {
    	return mk_mix(p().hash(), q().hash(), mk_mix(kind(), is_overflow(), 0));
    }

    bool smul_fl_constraint::operator==(constraint const& other) const {
        return other.is_smul_fl()
            && is_overflow() == other.to_smul_fl().is_overflow()
            && p() == other.to_smul_fl().p()
            && q() == other.to_smul_fl().q();
    }

    void smul_fl_constraint::add_to_univariate_solver(pvar v, solver& s, univariate_solver& us, unsigned dep, bool is_positive) const {
        auto p1 = s.subst(p());
        if (!p1.is_univariate_in(v))
            return;
        auto q1 = s.subst(q());
        if (!q1.is_univariate_in(v))
            return;
        if (is_overflow())
            us.add_smul_ovfl(p1.get_univariate_coefficients(), q1.get_univariate_coefficients(), !is_positive, dep);
        else
            us.add_smul_udfl(p1.get_univariate_coefficients(), q1.get_univariate_coefficients(), !is_positive, dep);
    }

}
