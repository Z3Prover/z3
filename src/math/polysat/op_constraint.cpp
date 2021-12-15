/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat shift right constraint.

Author:

    Jakob Rath, Nikolaj Bjorner (nbjorner) 2021-12-09

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
    
    std::ostream& op_constraint::display(std::ostream& out, lbool status) const {
        switch (status) {
        case l_true: return display(out);
        case l_false: return display(out << "~");
        default: return display(out << "?");
        }
    }

    std::ostream& operator<<(std::ostream & out, op_constraint::code c) {
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
            return out << "?";
        }
        return out;
    }

    std::ostream& op_constraint::display(std::ostream& out) const {
        return out << r() << " " << m_op << " " << p() << " << " << q();                
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

    void op_constraint::narrow(solver& s, bool is_positive) {
        SASSERT(is_positive);
        switch (m_op) {
        case code::lshr_op:
            narrow_lshr(s);
            break;
        default:
            NOT_IMPLEMENTED_YET();
            break;
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
     * Enforce basic axioms, such as:
     *
     * r = p >> q & q >= k -> r[i] = 0 for i > K - k
     * r = p >> q & q >= K -> r = 0
     * r = p >> q & q = k -> r[i] = p[i+k] for k + i < K
     * r = p >> q & q >= k -> r <= 2^{K-k-1}
     * r = p >> q => r <= p
     * r = p >> q & q != 0 => r < p
     * r = p >> q & q = 0 => r = p
     *
     * when q is a constant, several axioms can be enforced at activation time.
     *
     * Enforce also inferences and bounds
     *
     * We can assume that op_constraint is only asserted positive.
     */
    void op_constraint::narrow_lshr(solver& s) {
        NOT_IMPLEMENTED_YET();
    }

    lbool op_constraint::eval_lshr(pdd const& p, pdd const& q, pdd const& r) const {
        if (q.is_val() && r.is_val()) {
            auto& m = p.manager();
            if (q.val() >= m.power_of_2())
                return r.is_zero() ? l_true : l_false;
            if (p.is_val()) {
                pdd rr = p * m.mk_val(rational::power_of_two(q.val().get_unsigned()));
                return rr == r ? l_true : l_false;
            }
            // other cases when we know lower 
            // bound of q, e.g, q = 2^k*q1 + q2, where q2 is a constant.
        }
        return l_undef;
    }
}
