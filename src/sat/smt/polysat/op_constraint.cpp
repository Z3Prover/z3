/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat constraints for bit operations.

Author:

    Jakob Rath, Nikolaj Bjorner (nbjorner) 2021-12-09

Notes:

Additional possible functionality on constraints:

- bit-wise assignments - narrow based on bit assignment, not entire word assignment.
- integration with congruence tables
- integration with conflict resolution

--*/

#include "util/log.h"
#include "sat/smt/polysat/op_constraint.h"
#include "sat/smt/polysat/core.h"

namespace polysat {

    op_constraint::op_constraint(code c, pdd const& _p, pdd const& _q, pdd const& _r) :
        m_op(c), p(_p), q(_q), r(_r) {
        vars().append(p.free_vars());
        for (auto v : q.free_vars())
            if (!vars().contains(v))
                vars().push_back(v);
        for (auto v : r.free_vars())
            if (!vars().contains(v))
                vars().push_back(v);

        switch (c) {
        case code::and_op:
            if (p.index() > q.index())
                std::swap(p, q);
            break;
        case code::inv_op:
            SASSERT(q.is_zero());
            break;
        default:
            break;
        }
        VERIFY(r.is_var());
    }

    lbool op_constraint::eval() const {
        return eval(p, q, r);
    }

    lbool op_constraint::eval(assignment const& a) const {
        return eval(a.apply_to(p), a.apply_to(q), a.apply_to(r));
    }

    lbool op_constraint::eval(pdd const& p, pdd const& q, pdd const& r) const {
        switch (m_op) {
        case code::lshr_op:
            return eval_lshr(p, q, r);
        case code::shl_op:
            return eval_shl(p, q, r);
        case code::and_op:
            return eval_and(p, q, r);
        case code::inv_op:
            return eval_inv(p, r);
        case code::ashr_op:
            return eval_ashr(p, q, r);
        default:
            return l_undef;
        }
    }


    /** Evaluate constraint: r == p >> q */
    lbool op_constraint::eval_lshr(pdd const& p, pdd const& q, pdd const& r) {
        auto& m = p.manager();

        if (q.is_zero() && p == r)
            return l_true;

        if (q.is_val() && q.val() >= m.power_of_2() && r.is_val())
            return to_lbool(r.is_zero());

        if (p.is_val() && q.is_val() && r.is_val()) {
            SASSERT(q.val().is_unsigned());  // otherwise, previous condition should have been triggered
            return to_lbool(r.val() == machine_div2k(p.val(), q.val().get_unsigned()));
        }

        // TODO: other cases when we know lower bound of q,
        //       e.g, q = 2^k*q1 + q2, where q2 is a constant.
        return l_undef;
    }

    lbool op_constraint::eval_ashr(pdd const& p, pdd const& q, pdd const& r) {
        auto& m = p.manager();
        if (r.is_val() && p.is_val() && q.is_val()) {
            auto M = m.max_value();
            auto N = M + 1;
            if (p.val() >= N/2) {
                if (q.val() >= m.power_of_2())
                    return to_lbool(r.val() == M);
                unsigned k = q.val().get_unsigned();
                return to_lbool(r.val() == p.val() - rational::power_of_two(k));
            }
            else
                return eval_lshr(p, q, r);
        }
        if (q.is_val() && q.is_zero() && p == r)
            return l_true;
        return l_undef;
    }

    /** Evaluate constraint: r == p << q */
    lbool op_constraint::eval_shl(pdd const& p, pdd const& q, pdd const& r) {
        auto& m = p.manager();

        if (q.is_zero() && p == r)
            return l_true;

        if (q.is_val() && q.val() >= m.power_of_2() && r.is_val())
            return to_lbool(r.is_zero());

        if (p.is_val() && q.is_val() && r.is_val()) {
            SASSERT(q.val().is_unsigned());  // otherwise, previous condition should have been triggered
            // TODO: use left-shift operation instead of multiplication?
            auto factor = rational::power_of_two(q.val().get_unsigned());
            return to_lbool(r == p * m.mk_val(factor));
        }

        // TODO: other cases when we know lower bound of q,
        //       e.g, q = 2^k*q1 + q2, where q2 is a constant.
        //       (bounds should be tracked by viable, then just use min_viable here)
        return l_undef;
    }

    /** Evaluate constraint: r == p & q */
    lbool op_constraint::eval_and(pdd const& p, pdd const& q, pdd const& r) {
        if ((p.is_zero() || q.is_zero()) && r.is_zero())
            return l_true;

        if (p.is_val() && q.is_val() && r.is_val())
            return r.val() == bitwise_and(p.val(), q.val()) ? l_true : l_false;

        return l_undef;
    }

    /** Evaluate constraint: r == inv p */
    lbool op_constraint::eval_inv(pdd const& p, pdd const& r) {
        if (!p.is_val() || !r.is_val())
            return l_undef;

        if (p.is_zero() || r.is_zero()) // the inverse of 0 is 0 (by arbitrary definition). Just to have some unique value
            return to_lbool(p.is_zero() && r.is_zero());

        return to_lbool(p.val().pseudo_inverse(p.power_of_2()) == r.val());
    }

    std::ostream& op_constraint::display(std::ostream& out, lbool status) const {
        switch (status) {
        case l_true: return display(out, "==");
        case l_false: return display(out, "!=");
        default: return display(out, "?=");
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
        case op_constraint::code::inv_op:
            return out << "inv";
        default:
            UNREACHABLE();
            return out;
        }
        return out;
    }

    std::ostream& op_constraint::display(std::ostream& out) const {
        return display(out, l_true);
    }

    std::ostream& op_constraint::display(std::ostream& out, char const* eq) const {
        if (m_op == code::inv_op)
            return out << r << " " << eq << " " << m_op << " " << p;

        return out << r << " " << eq << " " << p << " " << m_op << " " << q;
    }

    void op_constraint::activate(core& c, bool sign, dependency const& dep) {
        SASSERT(!sign);
        switch (m_op) {
        case code::and_op:
            activate_and(c, dep);
            break;
        case code::ashr_op:
            activate_ashr(c, dep);
            break;
        default:
            break;
        }
    }

    void op_constraint::propagate(core& c, lbool value, dependency const& dep) {
        SASSERT(value == l_true);
        switch (m_op) {
        case code::lshr_op:
            propagate_lshr(c, dep);
            break;
        case code::ashr_op:
            propagate_ashr(c, dep);
            break;
        case code::shl_op:
            propagate_shl(c, dep);
            break;
        case code::and_op:
            propagate_and(c, dep);
            break;
        case code::inv_op:
            propagate_inv(c, dep);
            break;
        default:
            verbose_stream() << "not implemented yet: " << *this << "\n";
            NOT_IMPLEMENTED_YET();
            break;
        }
    }

    void op_constraint::propagate_inv(core& s, dependency const& dep) {

    }

    /**
  * Enforce basic axioms for r == p >> q:
  *
  *      q >= N  ->  r = 0
  *      q >= k  ->  r[i] = 0 for N - k <= i < N     (bit indices range from 0 to N-1, inclusive)
  *      q >= k  ->  r <= 2^{N-k} - 1
  *      q = k   ->  r[i] = p[i+k] for 0 <= i < N - k
  *      r <= p
  *      q != 0  ->  r <= p      (subsumed by previous axiom)
  *      q != 0  /\  p > 0 ->  r < p
  *      q = 0   ->  r = p
  *      p = q   ->  r = 0
  *
  * when q is a constant, several axioms can be enforced at activation time.
  *
  * Enforce also inferences and bounds
  *
  * TODO: use also
  * s.m_viable.min_viable();
  * s.m_viable.max_viable()
  * when r, q are variables.
  */
    void op_constraint::propagate_lshr(core& c, dependency const& d) {
        auto& m = p.manager();
        auto const pv = c.subst(p);
        auto const qv = c.subst(q);
        auto const rv = c.subst(r);
        unsigned const N = m.power_of_2();

        auto& C = c.cs();

        if (pv.is_val() && rv.is_val() && rv.val() > pv.val())
            c.add_clause("lshr 1", { C.ule(r, p) }, false);

        else if (qv.is_val() && qv.val() >= N && rv.is_val() && !rv.is_zero())
            // TODO: instead of rv.is_val() && !rv.is_zero(), we should use !is_forced_zero(r) which checks whether eval(r) = 0 or bvalue(r=0) = true; see saturation.cpp
            c.add_clause("q >= N -> r = 0", { ~C.ule(N, q), C.eq(r) }, true);
        else if (qv.is_zero() && pv.is_val() && rv.is_val() && pv != rv)
            c.add_clause("q = 0 -> p = r", { ~C.eq(q), C.eq(p, r) } , true);
        else if (qv.is_val() && !qv.is_zero() && pv.is_val() && rv.is_val() && !pv.is_zero() && rv.val() >= pv.val())
            c.add_clause("q != 0 & p > 0 -> r < p", { C.eq(q), C.ule(p, 0), C.ult(r, p) }, true);
        else if (qv.is_val() && !qv.is_zero() && qv.val() < N && rv.is_val() && rv.val() > rational::power_of_two(N - qv.val().get_unsigned()) - 1)
            c.add_clause("q >= k -> r <= 2^{N-k} - 1", { ~C.ule(qv.val(), q), C.ule(r, rational::power_of_two(N - qv.val().get_unsigned()) - 1)}, true);
        else if (pv.is_val() && rv.is_val() && qv.is_val() && !qv.is_zero()) {
            unsigned k = qv.val().get_unsigned();
            for (unsigned i = 0; i < N - k; ++i) {
                if (rv.val().get_bit(i) && !pv.val().get_bit(i + k)) 
                    c.add_clause("q = k  ->  r[i] = p[i+k] for 0 <= i < N - k", { ~C.eq(q, k), ~C.bit(r, i), C.bit(p, i + k) }, true);
                
                if (!rv.val().get_bit(i) && pv.val().get_bit(i + k)) 
                    c.add_clause("q = k  ->  r[i] = p[i+k] for 0 <= i < N - k", { ~C.eq(q, k), C.bit(r, i), ~C.bit(p, i + k) }, true);                
            }
        }
        else {
            // forward propagation
            SASSERT(!(pv.is_val() && qv.is_val() && rv.is_val()));
            // LOG(p << " = " << pv << " and " << q << " = " << qv << " yields [>>] " << r << " = " << (qv.val().is_unsigned() ? machine_div2k(pv.val(), qv.val().get_unsigned()) : rational::zero()));
            if (qv.is_val() && !rv.is_val()) {
                rational const& q_val = qv.val();
                if (q_val >= N)
                    // q >= N ==> r = 0
                    c.add_clause("q >= N ==> r = 0", { ~C.ule(N, q), C.eq(r) }, true);
                else if (pv.is_val()) {
                    SASSERT(q_val.is_unsigned());
                    // 
                    rational const r_val = machine_div2k(pv.val(), q_val.get_unsigned());
                    c.add_clause("p = p_val & q = q_val ==> r = p_val / 2^q_val", { ~C.eq(p, pv), ~C.eq(q, qv), C.eq(r, r_val) }, true);
                }
            }
        }
    }

    void op_constraint::activate_ashr(core& c, dependency const& d) {
        auto& m = p.manager();
        unsigned const N = m.power_of_2();
        auto& C = c.cs();
        c.add_clause("q >= N & p < 0 -> p << q = -1", {~C.uge(q, N), ~C.slt(p, 0), C.eq(r, m.max_value())}, false);
        c.add_clause("q >= N & p >= 0 -> p << q = 0", {~C.uge(q, N), ~C.sge(p, 0), C.eq(r)}, false);
        c.add_clause("q = 0 -> p << q = p", { ~C.eq(q), C.eq(r, p) }, false);
    }


    void op_constraint::activate_and(core& c, dependency const& d) {
        auto x = p, y = q;
        auto& C = c.cs();

        c.add_clause("band-mask p&q <= p", { C.ule(r, p) }, false);
        c.add_clause("band-mask p&q <= q", { C.ule(r, q) }, false);

        if (x.is_val())
            std::swap(x, y);
        if (!y.is_val())
            return;
        auto& m = x.manager();
        auto yv = y.val();
        if (!(yv + 1).is_power_of_two())
            return;
        if (yv == m.max_value())
            c.add_clause("band-mask-true", { C.eq(x, r) }, false);
        else if (yv == 0)
            c.add_clause("band-mask-false", { C.eq(r) }, false);
        else {
            unsigned N = m.power_of_2();
            unsigned k = yv.get_num_bits();
            SASSERT(k < N);
            rational exp = rational::power_of_two(N - k);
            c.add_clause("band-mask 1", { C.eq(x * exp, r * exp) }, false);
        }
    }   

    void op_constraint::propagate_ashr(core& c, dependency const& dep) {
        //
        // Suppose q = k, p >= 0:
        // p = ab, where b has length k, a has length N - k
        // r = 0a, where 0 has length k, a has length N - k
        // r*2^k = a0
        // ab - a0 = 0b = p - r*2^k < 2^k
        // r < 2^{N-k}
        // 
        // Suppose q = k, p < 0
        // p = ab
        // r = 111a where 111 has length k
        // r*2^k = a0
        // ab - a0 = 0b = p - r*2^k < 2^k
        // r >= 1110
        // example:
        //    1100 = 12 = 16 - 4 = 2^4 - 2^2 = 2^N - 2^k
        // 
        // Succinct:
        // if q = k & p >= 0 -> r*2^k + p < 2^{N-k} && r < 2^k
        // if q = k & p < 0  -> (p / 2^k) - 2^N + 2^{N-k}
        //
        auto& m = p.manager();
        auto N = m.power_of_2();
        auto qv = c.subst(q);
        if (qv.is_val() && 1 <= qv.val() && qv.val() < N) {
            auto pv = c.subst(p);
            auto rv = c.subst(r);
            auto& C = c.cs();
            unsigned k = qv.val().get_unsigned();
            rational twoN = rational::power_of_two(N);
            rational twoK = rational::power_of_two(k);
            rational twoNk = rational::power_of_two(N - k);
            auto eqK = C.eq(q, k);
            c.add_clause("q = k -> r*2^k + p < 2^k", { ~eqK, C.ult(p - r * twoK, twoK) }, true);
            c.add_clause("q = k & p >= 0 -> r < 2^{N-k}", { ~eqK, ~C.ule(0, p), C.ult(r, twoNk) }, true);            
            c.add_clause("q = k & p < 0 -> r >= 2^N - 2^{N-k}", { ~eqK, ~C.slt(p, 0), C.uge(r, twoN - twoNk) }, true);
        }
    }


    /**
     * Enforce axioms for constraint: r == p << q
     *
     *      q >= N  ->  r = 0
     *      q >= k  ->  r = 0  \/  r >= 2^k
     *      q >= k  ->  r[i] = 0 for i < k
     *      q = k   ->  r[i+k] = p[i] for 0 <= i < N - k
     *      q = 0   ->  r = p
     */
    void op_constraint::propagate_shl(core& c, dependency const& d) {
        auto& m = p.manager();
        auto const pv = c.subst(p);
        auto const qv = c.subst(q);
        auto const rv = c.subst(r);
        unsigned const N = m.power_of_2();
        auto& C = c.cs();

        if (qv.is_val() && qv.val() >= N && rv.is_val() && !rv.is_zero())            
            c.add_clause("q >= N  ->  r = 0", { ~C.ule(N, q), C.eq(r) }, true);
        else if (qv.is_zero() && pv.is_val() && rv.is_val() && rv != pv)
            // 
            c.add_clause("q = 0  ->  r = p", { ~C.eq(q), C.eq(r, p) }, true);
        else if (qv.is_val() && !qv.is_zero() && qv.val() < N && rv.is_val() &&
            !rv.is_zero() && rv.val() < rational::power_of_two(qv.val().get_unsigned()))
            // q >= k  ->  r = 0  \/  r >= 2^k  (intuitive version)
            // q >= k  ->  r - 1 >= 2^k - 1     (equivalent unit constraint to better support narrowing)
            c.add_clause("q >= k  ->  r - 1 >= 2^k - 1", { ~C.ule(qv.val(), q), C.ule(rational::power_of_two(qv.val().get_unsigned()) - 1, r - 1) }, true);
        else if (pv.is_val() && rv.is_val() && qv.is_val() && !qv.is_zero()) {
            unsigned k = qv.val().get_unsigned();
            // q = k  ->  r[i+k] = p[i] for 0 <= i < N - k
            for (unsigned i = 0; i < N - k; ++i) {
                if (rv.val().get_bit(i + k) && !pv.val().get_bit(i)) {
                    c.add_clause("q = k  ->  r[i+k] = p[i] for 0 <= i < N - k", { ~C.eq(q, k), ~C.bit(r, i + k), C.bit(p, i) }, true);
                }
                if (!rv.val().get_bit(i + k) && pv.val().get_bit(i)) {
                    c.add_clause("q = k  ->  r[i+k] = p[i] for 0 <= i < N - k", { ~C.eq(q, k), C.bit(r, i + k), ~C.bit(p, i) }, true);
                }
            }
        }
        else {
            // forward propagation
            SASSERT(!(pv.is_val() && qv.is_val() && rv.is_val()));
            // LOG(p << " = " << pv << " and " << q << " = " << qv << " yields [<<] " << r << " = " << (qv.val().is_unsigned() ? rational::power_of_two(qv.val().get_unsigned()) * pv.val() : rational::zero()));
            if (qv.is_val() && !rv.is_val()) {
                rational const& q_val = qv.val();
                if (q_val >= N)
                    // q >= N ==> r = 0
                    c.add_clause("shl forward 1", {~C.ule(N, q), C.eq(r)}, true);
                if (pv.is_val()) {
                    SASSERT(q_val.is_unsigned());
                    // p = p_val & q = q_val ==> r = p_val * 2^q_val
                    rational const r_val = pv.val() * rational::power_of_two(q_val.get_unsigned());
                    c.add_clause("shl forward 2", {~C.eq(p, pv), ~C.eq(q, qv), C.eq(r, r_val)}, true);
                }
            }
        }
    }

    /**
     * Produce lemmas for constraint: r == p & q
     * r <= p
     * r <= q
     * p = q => r = p
     * p[i] && q[i] = r[i]
     * p = 2^N - 1 => q = r
     * q = 2^N - 1 => p = r
     * p = 2^k - 1 => r*2^{N - k} = q*2^{N - k}
     * q = 2^k - 1 => r*2^{N - k} = p*2^{N - k}
     * p = 2^k - 1 && r = 0 && q != 0 => q >= 2^k
     * q = 2^k - 1 && r = 0 && p != 0 => p >= 2^k
     */
    void op_constraint::propagate_and(core& c, dependency const& d) {
        auto& m = p.manager();
        auto pv = c.subst(p);
        auto qv = c.subst(q);
        auto rv = c.subst(r);
        auto& C = c.cs();

        if (pv.is_val() && rv.is_val() && rv.val() > pv.val())
            c.add_clause("p&q <= p", { C.ule(r, p) }, true);
        else if (qv.is_val() && rv.is_val() && rv.val() > qv.val())
            c.add_clause("p&q <= q", { C.ule(r, q) }, true);
        else if (pv.is_val() && qv.is_val() && rv.is_val() && pv == qv && rv != pv)
            c.add_clause("p = q => r = p", { ~C.eq(p, q), C.eq(r, p) }, true);
        else if (pv.is_val() && qv.is_val() && rv.is_val()) {
            if (pv.is_max() && qv != rv)
                c.add_clause("p = -1 => r = q", { ~C.eq(p, m.max_value()), C.eq(q, r) }, true);
            if (qv.is_max() && pv != rv)
                c.add_clause("q = -1 => r = p", { ~C.eq(q, m.max_value()), C.eq(p, r) }, true);

            unsigned const N = m.power_of_2();
            unsigned pow;
            if ((pv.val() + 1).is_power_of_two(pow)) {
                if (rv.is_zero() && !qv.is_zero() && qv.val() <= pv.val())
                    c.add_clause("p = 2^k - 1 && r = 0 && q != 0 => q >= 2^k", { ~C.eq(p, pv), ~C.eq(r), C.eq(q), C.ule(pv + 1, q) }, true);
                if (rv != qv)
                    c.add_clause("p = 2^k - 1  ==>  r*2^{N - k} = q*2^{N - k}", { ~C.eq(p, pv), C.eq(r * rational::power_of_two(N - pow), q * rational::power_of_two(N - pow)) }, true);
            }
            if ((qv.val() + 1).is_power_of_two(pow)) {
                if (rv.is_zero() && !pv.is_zero() && pv.val() <= qv.val())
                    c.add_clause("q = 2^k - 1 && r = 0 && p != 0  ==>  p >= 2^k", { ~C.eq(q, qv), ~C.eq(r), C.eq(p), C.ule(qv + 1, p) }, true);
                // 
                if (rv != pv)
                    c.add_clause("q = 2^k - 1  ==>  r*2^{N - k} = p*2^{N - k}", { ~C.eq(q, qv), C.eq(r * rational::power_of_two(N - pow), p * rational::power_of_two(N - pow)) }, true);
            }

            for (unsigned i = 0; i < N; ++i) {
                bool pb = pv.val().get_bit(i);
                bool qb = qv.val().get_bit(i);
                bool rb = rv.val().get_bit(i);
                if (rb == (pb && qb))
                    continue;
                if (pb && qb && !rb)
                    c.add_clause("p&q[i] = p[i]&q[i]", { ~C.bit(p, i), ~C.bit(q, i), C.bit(r, i) }, true);
                else if (!pb && rb)
                    c.add_clause("p&q[i] = p[i]&q[i]", { C.bit(p, i), ~C.bit(r, i) }, true);
                else if (!qb && rb)
                    c.add_clause("p&q[i] = p[i]&q[i]", { C.bit(q, i), ~C.bit(r, i) }, true);
                else
                    UNREACHABLE();
            }
            return;
        }

        // Propagate r if p or q are 0
        else if (pv.is_zero() && !rv.is_zero())  // rv not necessarily fully evaluated
            c.add_clause("p = 0 -> p&q = 0", { C.ule(r, p) }, true);
        else if (qv.is_zero() && !rv.is_zero())  // rv not necessarily fully evaluated
            c.add_clause("q = 0 -> p&q = 0", { C.ule(r, q) }, true);
        // p = a && q = b ==> r = a & b
        else if (pv.is_val() && qv.is_val() && !rv.is_val()) {
            // Just assign by this very weak justification. It will be strengthened in saturation in case of a conflict
            LOG(p << " = " << pv << " and " << q << " = " << qv << " yields [band] " << r << " = " << bitwise_and(pv.val(), qv.val()));
            c.add_clause("p = a & q = b => r = a&b", { ~C.eq(p, pv), ~C.eq(q, qv), C.eq(r, bitwise_and(pv.val(), qv.val())) }, true);
        }
    }

#if 0

    /**
     * Produce lemmas for constraint: r == inv p
     * p = 0   ==>  r = 0
     * r = 0   ==>  p = 0
     * p != 0  ==>  odd(r)
     * parity(p) >= k   ==>  p * r >= 2^k
     * parity(p) < k    ==>  p * r <= 2^k - 1
     * parity(p) < k    ==>  r <= 2^(N - k) - 1     (because r is the smallest pseudo-inverse)
     */
    clause_ref op_constraint::lemma_inv(solver& s, assignment const& a) {
        auto& m = p.manager();
        auto pv = a.apply_to(p);
        auto rv = a.apply_to(r);

        if (eval_inv(pv, rv) == l_true)
            return {};

        signed_constraint const invc(this, true);

        // p = 0  ==>  r = 0
        if (pv.is_zero())
            c.add_clause(~invc, ~C.eq(p), C.eq(r), true);
        // r = 0  ==>  p = 0
        if (rv.is_zero())
            c.add_clause(~invc, ~C.eq(r), C.eq(p), true);

        // forward propagation: p assigned  ==>  r = pseudo_inverse(eval(p))
        // TODO: (later) this should be propagated instead of adding a clause
        /*if (pv.is_val() && !rv.is_val())
            c.add_clause(~invc, ~C.eq(p, pv), C.eq(r, pv.val().pseudo_inverse(m.power_of_2())), true);*/

        if (!pv.is_val() || !rv.is_val())
            return {};

        unsigned parity_pv = pv.val().trailing_zeros();
        unsigned parity_rv = rv.val().trailing_zeros();

        LOG("p: " << p << " := " << pv << "   parity " << parity_pv);
        LOG("r: " << r << " := " << rv << "   parity " << parity_rv);

        // p != 0  ==>  odd(r)
        if (parity_rv != 0)
            c.add_clause("r = inv p  &  p != 0  ==>  odd(r)", {~invc, C.eq(p), s.odd(r)}, true);

        pdd prod = p * r;
        rational prodv = (pv * rv).val();
//        if (prodv != rational::power_of_two(parity_pv))
//            verbose_stream() << prodv << " " << rational::power_of_two(parity_pv) << " " << parity_pv << " " << pv << " " << rv << "\n";
        unsigned lower = 0, upper = m.power_of_2();
        // binary search for the parity (otw. we would have justifications like "parity_at_most(k) && parity_at_least(k)" for at most "k" widths
        while (lower + 1 < upper) {
            unsigned middle = (upper + lower) / 2;
            LOG("Splitting on " << middle);
            if (parity_pv >= middle) { // parity at least middle
                lower = middle;
                LOG("Its in [" << lower << "; " << upper << ")");
                // parity(p) >= k  ==>  p * r >= 2^k
                if (prodv < rational::power_of_two(middle))
                    c.add_clause("r = inv p  &  parity(p) >= k  ==>  p*r >= 2^k",
                        {~invc, ~s.parity_at_least(p, middle), s.uge(prod, rational::power_of_two(middle))}, false);
                // parity(p) >= k  ==>  r <= 2^(N - k) - 1     (because r is the smallest pseudo-inverse)
                rational const max_rv = rational::power_of_two(m.power_of_2() - middle) - 1;
                if (rv.val() > max_rv)
                    c.add_clause("r = inv p  &  parity(p) >= k  ==>  r <= 2^(N - k) - 1",
                        {~invc, ~s.parity_at_least(p, middle), C.ule(r, max_rv)}, false);
            }
            else { // parity less than middle
                SASSERT(parity_pv < middle);
                upper = middle;
                LOG("Its in [" << lower << "; " << upper << ")");
                // parity(p) < k   ==>  p * r <= 2^k - 1
                if (prodv > rational::power_of_two(middle))
                    c.add_clause("r = inv p  &  parity(p) < k  ==>  p*r <= 2^k - 1",
                        {~invc, s.parity_at_least(p, middle), C.ule(prod, rational::power_of_two(middle) - 1)}, false);
            }
        }
         // Why did it evaluate to false in this case?
        UNREACHABLE();
        return {};
    }

#endif
}
