/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat constraints for bit operations.

Author:

    Jakob Rath, Nikolaj Bjorner (nbjorner) 2021-12-09

Notes:

Additional possible functionality on constraints:

- activate - when operation is first activated. It may be created and only activated later.
- bit-wise assignments - narrow based on bit assignment, not entire word assignment.
- integration with congruence tables
- integration with conflict resolution

--*/

#include "math/polysat/op_constraint.h"
#include "math/polysat/solver.h"

namespace polysat {

    op_constraint::op_constraint(constraint_manager& m, code c, pdd const& p, pdd const& q, pdd const& r):
        constraint(m, ckind_t::op_t), m_op(c), m_p(p), m_q(q), m_r(r) {
        m_vars.append(p.free_vars());
        for (auto v : q.free_vars())
            if (!m_vars.contains(v))
                m_vars.push_back(v);
        for (auto v : r.free_vars())
            if (!m_vars.contains(v))
                m_vars.push_back(v);
    }    

    lbool op_constraint::eval(pdd const& p, pdd const& q, pdd const& r) const {
        switch (m_op) {
        case code::lshr_op:
            return eval_lshr(p, q, r);         
        default:
            return l_undef;            
        }       
    }
    
    bool op_constraint::is_always_false(bool is_positive, pdd const& p, pdd const& q, pdd const& r) const {
        switch (eval(p, q, r)) {
        case l_true: return !is_positive;
        case l_false: return is_positive;
        default: return false;
        }
    }

    bool op_constraint::is_always_true(bool is_positive, pdd const& p, pdd const& q, pdd const& r) const {
        switch (eval(p, q, r)) {
        case l_true: return is_positive;
        case l_false: return !is_positive;
        default: return false;
        }
    }

    bool op_constraint::is_always_false(bool is_positive) const {
        return is_always_false(is_positive, p(), q(), r());
    }

    bool op_constraint::is_currently_false(assignment_t const& a, bool is_positive) const {
        return is_always_false(is_positive, p().subst_val(a), q().subst_val(a), r().subst_val(a));
    }

    bool op_constraint::is_currently_true(assignment_t const& a, bool is_positive) const {
        return is_always_true(is_positive, p().subst_val(a), q().subst_val(a), r().subst_val(a));
    }

    std::ostream& op_constraint::display(std::ostream& out, lbool status) const {
        switch (status) {
        case l_true: return display(out);
        case l_false: return display(out << "~");
        default: return display(out << "?");
        }
    }

    std::ostream& operator<<(std::ostream& out, op_constraint::code c) {
        switch (c) {
        case op_constraint::code::ashr_op:
            return out << ">>a";
        case op_constraint::code::lshr_op:
            return out << ">>";
        case op_constraint::code::shl_op:
            return out << "<<";
        case op_constraint::code::and_op:
            return out << "&";
        case op_constraint::code::or_op:
            return out << "|";
        case op_constraint::code::xor_op:
            return out << "^";
        default:
            UNREACHABLE();
            return out;
        }
        return out;
    }

    std::ostream& op_constraint::display(std::ostream& out) const {
        if (m_op == code::not_op)
            return out << r() << " == ~" << p();
        else
            return out << r() << " == " << p() << " " << m_op << " " << q();
    }

    /**
    * Propagate consequences or detect conflicts based on partial assignments.
    * 
    * We can assume that op_constraint is only asserted positive.
    */

    void op_constraint::narrow(solver& s, bool is_positive) {
        SASSERT(is_positive);

        if (is_currently_true(s.assignment(), is_positive))
            return;

        switch (m_op) {
        case code::lshr_op:
            narrow_lshr(s);
            break;
        default:
            NOT_IMPLEMENTED_YET();
            break;
        }
        if (!s.is_conflict() && is_currently_false(s.assignment(), is_positive)) {
            s.set_conflict(signed_constraint(this, is_positive));
            return;
        }
    }

    unsigned op_constraint::hash() const {
        return mk_mix(p().hash(), q().hash(), r().hash());
    }

    bool op_constraint::operator==(constraint const& other) const {
        if (other.kind() != ckind_t::op_t)
            return false;
        auto const& o = other.to_op();
        return m_op == o.m_op && p() == o.p() && q() == o.q() && r() == o.r();
    }

    /**
     * Enforce basic axioms for r == p >> q, such as:
     *
     * q >= k -> r[i] = 0 for i > K - k
     * q >= K -> r = 0
     * q = k -> r[i] = p[i+k] for k + i < K
     * q >= k -> r <= 2^{K-k-1}
     * r <= p
     * q != 0 => r <= p
     * q = 0 => r = p
     *
     * when q is a constant, several axioms can be enforced at activation time.
     *
     * Enforce also inferences and bounds
     *
     */
    void op_constraint::narrow_lshr(solver& s) {
        auto pv = p().subst_val(s.assignment());
        auto qv = q().subst_val(s.assignment());
        auto rv = r().subst_val(s.assignment());
        unsigned K = p().manager().power_of_2();
        signed_constraint lshr(this, true);
        // r <= p
        if (pv.is_val() && rv.is_val() && rv.val() > pv.val()) {
            s.add_clause(~lshr, s.ule(r(), p()), true);
            return;
        }
        // q >= K -> r = 0
        if (qv.is_val() && qv.val() >= K && rv.is_val() && !rv.is_zero()) {
            s.add_clause(~lshr, ~s.ule(K, q()), s.eq(r()), true);
            return;
        }
        // q = 0 => r = p
        if (qv.is_zero() && pv.is_val() && rv.is_val() && pv != rv) {
            s.add_clause(~lshr, ~s.eq(q()), s.eq(p(), r()), true);
            return;
        }
        // q != 0 & p > 0 => r < p
        if (qv.is_val() && !qv.is_zero() && pv.is_val() && rv.is_val() && !pv.is_zero() && pv <= rv) {
            s.add_clause(~lshr, s.eq(q()), s.ule(p, 0), s.ult(r(), p()), true);
            return;
        }
        NOT_IMPLEMENTED_YET();
    }

    lbool op_constraint::eval_lshr(pdd const& p, pdd const& q, pdd const& r) const {
        auto& m = p.manager();

        if (p.is_val() && q.is_val() && r.is_val())
            return r == p * m.mk_val(rational::power_of_two(q.val().get_unsigned())) ? l_true : l_false;
            
        if (q.is_val() && q.val() >= m.power_of_2() && r.is_val())
            return r.is_zero() ? l_true : l_false;
        
        // other cases when we know lower 
        // bound of q, e.g, q = 2^k*q1 + q2, where q2 is a constant.
        return l_undef;
    }
}
