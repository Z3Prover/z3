/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat constraints for bit operations.

Author:

    Jakob Rath, Nikolaj Bjorner (nbjorner) 2021-12-09

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
        case code::and_op: Z3_fallthrough;
        case code::or_op:
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

    lbool op_constraint::weak_eval(assignment const& a) const {
        return eval();
    }

    lbool op_constraint::strong_eval(assignment const& a) const {
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
        case code::or_op:
            return eval_or(p, q, r);
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
            if (p.val() >= N / 2) {
                if (q.val() >= m.power_of_2()) {
                    if (p.is_zero())
                        return to_lbool(r.val() == 0);
                    else
                        return to_lbool(r.val() == M);
                }
                unsigned k = q.val().get_unsigned();
                // p >>a q = p / 2^k - 2^{N-k}
                auto pdiv2k = machine_div2k(p.val(), k);
                auto pNk = rational::power_of_two(m.power_of_2() - k);
                return to_lbool(r.val() == pdiv2k + N - pNk);
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

    /** Evaluate constraint: r == p | q */
    lbool op_constraint::eval_or(pdd const& p, pdd const& q, pdd const& r) {
        if (p.is_zero() && q == r)
            return l_true;
        if (q.is_zero() && p == r)
            return l_true;

        if (p.is_val() && q.is_val() && r.is_val())
            return r.val() == bitwise_or(p.val(), q.val()) ? l_true : l_false;

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
            return out << ">>l";
        case op_constraint::code::shl_op:
            return out << "<<";
        case op_constraint::code::and_op:
            return out << "&";
        case op_constraint::code::or_op:
            return out << "|";
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
        auto& m = p.manager();
        unsigned const N = m.power_of_2();
        auto& C = c.cs();
        SASSERT(!sign);
        switch (m_op) {
        case code::and_op:
            c.add_axiom("p & q <= p", { C.ule(r, q) }, false);
            c.add_axiom("p & q <= q", { C.ule(r, q) }, false);
            c.add_axiom("p = q -> p & q = p", { ~C.eq(p, q), C.eq(r, p) }, false);
            c.add_axiom("p & 0 = 0", { ~C.eq(q), C.eq(r) }, false);
            c.add_axiom("0 & q = 0", { ~C.eq(p), C.eq(r) }, false);
            c.add_axiom("1 & q = q", { ~C.eq(p, m.max_value()), C.eq(r, q) }, false);
            c.add_axiom("p & 1 = q", { ~C.eq(q, m.max_value()), C.eq(r, p) }, false);
            break;
        case code::or_op:
            c.add_axiom("p | q >= p", { C.ule(p, r) }, false);
            c.add_axiom("p | q >= q", { C.ule(q, r) }, false);
            c.add_axiom("p = q -> p | q = p", { ~C.eq(p, q), C.eq(r, p) }, false);
            c.add_axiom("p | 0 = p", { ~C.eq(q), C.eq(r, p) }, false);
            c.add_axiom("0 | q = q", { ~C.eq(p), C.eq(r, q) }, false);
            c.add_axiom("1 | q = 1", { ~C.eq(p, m.max_value()), C.eq(r, p) }, false);
            c.add_axiom("p | 1 = 1", { ~C.eq(q, m.max_value()), C.eq(r, q) }, false);
            break;
        case code::ashr_op:
            c.add_axiom("q >= N & p < 0 -> p >>a q = -1", { ~C.uge(q, N), ~C.slt(p, 0), C.eq(r, m.max_value()) }, false);
            c.add_axiom("q >= N & p >= 0 -> p >>a q = 0", { ~C.uge(q, N), ~C.sge(p, 0), C.eq(r) }, false);
            c.add_axiom("q = 0 -> p >>a q = p", { ~C.eq(q), C.eq(r, p) }, false);
            c.add_axiom("p = 0 -> p >>a q = p", { ~C.eq(p), C.eq(r, p) }, false);
            // resolvent of the first two axioms, independent of p
            c.add_axiom("q >= N -> p >>a q in {-1, 0}", { ~C.uge(q, N), C.ule(r + 1, 1) }, false);
            break;
        case code::lshr_op:
            c.add_axiom("q >= N  -> p >>l q = 0", { ~C.uge(q, N), C.eq(r) }, false);
            c.add_axiom("q = 0 -> p >>l q = p", { ~C.eq(q), C.eq(r, p) }, false);
            c.add_axiom("p = 0 -> p >>l q = p", { ~C.eq(p), C.eq(r, p) }, false);
            c.add_axiom("p >>l q <= p", { C.ule(r, p) }, false);
            break;
        case code::shl_op:
            c.add_axiom("q >= N -> p << q = 0", { ~C.uge(q, N), C.eq(r) }, false);
            c.add_axiom("q = 0 -> p << q = p", { ~C.eq(q), C.eq(r, p) }, false);
            break;
        case code::inv_op:
            break;
        default:
            break;
        }
    }

    bool op_constraint::saturate(core& c, lbool value, dependency const& dep) {
        SASSERT(value == l_true);
        switch (m_op) {
        case code::lshr_op:
            return saturate_lshr(c);
        case code::ashr_op:
            return saturate_ashr(c);
        case code::shl_op:
            return saturate_shl(c);            
        case code::and_op:
            return saturate_and(c);            
        case code::or_op:
            return saturate_or(c);            
        case code::inv_op:
            return saturate_inv(c);            
        default:
            verbose_stream() << "not implemented yet: " << *this << "\n";
            NOT_IMPLEMENTED_YET();
            break;
        }
        return false;
    }

    bool op_constraint::saturate_inv(core& s) {
        return false;
    }

    bool op_constraint::propagate(core& c, signed_constraint const& sc) {
        if (c.weak_eval(sc) != l_true)
            return false;
        c.propagate(sc, c.explain_weak_eval(sc));
        return true;
    }

    bool op_constraint::add_conflict(core& c, char const* ax, constraint_or_dependency_list const& cs) {
        for (auto sc : cs)
            if (std::holds_alternative<signed_constraint>(sc) &&
                !propagate(c, ~*std::get_if<signed_constraint>(&sc)))
                return false;
            
        c.add_axiom(ax, cs, true);
        return true;
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
  */
    bool op_constraint::saturate_lshr(core& c) {
        auto& m = p.manager();
        auto const pv = c.subst(p);
        auto const qv = c.subst(q);
        auto const rv = c.subst(r);
        unsigned const N = m.power_of_2();

        auto& C = c.cs();

        if (!pv.is_val() || !qv.is_val() || !rv.is_val())
            return false;

        SASSERT(!qv.is_zero());
        SASSERT(qv.val() < N);

        auto k = qv.val().get_unsigned();

        // q = k &  0 < k < N => 2^k r <= p <= 2^k*x + 2^k - 1

        auto twoK = rational::power_of_two(k);
        auto twoNK = rational::power_of_two(N - k);
        bool c1 = add_conflict(c, "q = k & 0 < k < N -> 2^k (p >>l q) <= p", { ~C.eq(q, k), C.ule(r * twoK, p)});
        bool c2 = add_conflict(c, "q = k & 0 < k < N -> p <= 2^k*(p >>l q) + 2^k - 1", { ~C.eq(q, k), C.ule(p, r * twoK + twoK - 1) });
        bool c3 = add_conflict(c, "q = k & 0 < k < N -> (p >>l q) < 2^{N-k}", { ~C.eq(q, k), C.ult(r, twoNK) });
        return c1 || c2 || c3;        
    }

    bool op_constraint::saturate_ashr(core& c) {
        //
        // Suppose q = k, p >= 0:
        // p = ab, where b has length k, a has length N - k
        // r = 0a, where 0 has length k, a has length N - k
        // r*2^k = a0
        // ab - a0 = 0b = p - r*2^k < 2^k
        // r < 2^{N-k}
        // From p >= 0 we know a[N-k-1] = 0, thus:
        // r < 2^{N-k-1}
        //
        // Suppose q = k, p < 0
        // p = ab
        // r = 111a where 111 has length k
        // r*2^k = a0
        // ab - a0 = 0b = p - r*2^k < 2^k
        // r >= 1110
        // example:
        //    1100 = 12 = 16 - 4 = 2^4 - 2^2 = 2^N - 2^k
        //     ^^^ a
        // p = 1ab, where b has length k, a has length N - k - 1
        // r = 111a, where 111 has length k + 1
        // r >= 2^N - 2^{N-k-1}
        //
        // Succinct:
        // if q = k & p >= 0 -> r*2^k + p < 2^{N-k} && r < 2^k
        // if q = k & p < 0  -> (p / 2^k) - 2^N + 2^{N-k}
        //
        auto& m = p.manager();
        auto N = m.power_of_2();
        auto qv = c.subst(q);
        // std::cerr << "saturate_ashr: p " << p << " q " << q << " r " << r << "\n";
        // std::cerr << "               pv " << c.subst(p) << " qv " << qv << " rv " << c.subst(r) << "\n";
        // std::cerr << "               N " << N << "\n";
        if (qv.is_val() && 1 <= qv.val() && qv.val() < N) {
            auto pv = c.subst(p);
            auto rv = c.subst(r);
            auto& C = c.cs();
            unsigned k = qv.val().get_unsigned();
            rational twoN = rational::power_of_two(N);
            rational twoK = rational::power_of_two(k);
            rational twoNk1 = rational::power_of_two(N - k - 1);

            bool c1 = add_conflict(c, "q = k & 0 < k < N -> 2^k r <= p", { ~C.eq(q, k), C.ule(r * twoK, p) });
            bool c2 = add_conflict(c, "q = k & 0 < k < N -> p <= 2^k*r + 2^k - 1", { ~C.eq(q, k), C.ule(p, r * twoK + twoK - 1) });
            bool c3 = add_conflict(c, "p < 0 & q = k -> r >= 2^N - 2^{N-k-1}", { ~C.eq(q, k), ~C.slt(p, 0),  C.uge(r, twoN - twoNk1) });
            bool c4 = add_conflict(c, "p >= 0 & q = k -> r < 2^{N-k-1}", { ~C.eq(q, k), C.slt(p, 0),  C.ult(r, twoNk1)});
            return c1 || c2 || c3 || c4;
        }
        return false;
    }


    /**
     * Enforce axioms for constraint: r == p << q
     *
     *      q = k   ->  r = 2^k*p, 0 < k < N
     *  
     * Optional:
     *      q >= k  ->  r = 0  \/  r >= 2^k
     *      q >= k  ->  r[i] = 0 for i < k
     */
    bool op_constraint::saturate_shl(core& c) {
        auto& m = p.manager();
        auto const pv = c.subst(p);
        auto const qv = c.subst(q);
        auto const rv = c.subst(r);
        unsigned const N = m.power_of_2();
        auto& C = c.cs();

        if (!qv.is_val())
            return false;

        if (qv.is_zero() || qv.val() >= N)
            return false;

        auto k = qv.val().get_unsigned();

        auto twoK = rational::power_of_two(k);

        return add_conflict(c, "p << k = 2^k*p", { ~C.eq(q, k), C.eq(r, p * twoK) });
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
    bool op_constraint::saturate_and(core& c) {
        auto& m = p.manager();
        auto pv = c.subst(p);
        auto qv = c.subst(q);
        auto rv = c.subst(r);
        auto& C = c.cs();

        if (!pv.is_val() || !qv.is_val() || !rv.is_val())
            return false;

        if (eval_and(pv, qv, rv) == l_true)
            return false;

        if (propagate_mask(c, p, q, r, pv.val(), qv.val(), rv.val()))
            return true;

        if (propagate_mask(c, q, p, r, qv.val(), pv.val(), rv.val()))
            return true;

        unsigned const N = m.power_of_2();
        for (unsigned i = 0; i < N; ++i) {
            bool pb = pv.val().get_bit(i);
            bool qb = qv.val().get_bit(i);
            bool rb = rv.val().get_bit(i);
            if (rb == (pb && qb))
                continue;
            if (pb && qb && !rb)
                add_conflict(c, "p&q[i] = p[i]&q[i]", { ~C.bit(p, i), ~C.bit(q, i), C.bit(r, i) });
            else if (!pb && rb)
                add_conflict(c, "p&q[i] = p[i]&q[i]", { C.bit(p, i), ~C.bit(r, i) });
            else if (!qb && rb)
                add_conflict(c, "p&q[i] = p[i]&q[i]", { C.bit(q, i), ~C.bit(r, i) });
            else
                UNREACHABLE();
            return true;
        }
        return false;
    }

    bool op_constraint::saturate_or(core& c) {
        auto& m = p.manager();
        auto pv = c.subst(p);
        auto qv = c.subst(q);
        auto rv = c.subst(r);
        auto& C = c.cs();

        if (!pv.is_val() || !qv.is_val() || !rv.is_val())
            return false;

        if (eval_or(pv, qv, rv) == l_true)
            return false;

        if (pv.is_max() && pv != rv)
            return add_conflict(c, "p = -1 => p & q = p", { ~C.eq(p, m.max_value()), C.eq(p, r)});

        if (qv.is_max() && qv != rv)
            return add_conflict(c, "q = -1 => p & q = q", { ~C.eq(q, m.max_value()), C.eq(q, r) });

        unsigned const N = m.power_of_2();
        for (unsigned i = 0; i < N; ++i) {
            bool pb = pv.val().get_bit(i);
            bool qb = qv.val().get_bit(i);
            bool rb = rv.val().get_bit(i);
            if (rb == (pb || qb))
                continue;
            if (pb && !rb)
                add_conflict(c, "p[i] => (p|q)[i]", { ~C.bit(p, i), C.bit(r, i) });
            else if (qb && !rb)
                add_conflict(c, "q[i] => (p|q)[i]", { ~C.bit(q, i), C.bit(r, i) });
            else if (!pb && !qb && rb)
                add_conflict(c, "(p|q)[i] => p[i] or q[i]", { C.bit(p, i), C.bit(q, i), ~C.bit(r, i) });
            else
                UNREACHABLE();
            return true;
        }
        return false;
    }

    bool op_constraint::propagate_mask(core& c, pdd const& p, pdd const& q, pdd const& r, rational const& pv, rational const& qv, rational const& rv) {
        auto& m = p.manager();
        auto& C = c.cs();
        unsigned const N = m.power_of_2();
        unsigned pow;
        if (!(pv + 1).is_power_of_two(pow))
            return false;

        if (rv.is_zero() && !qv.is_zero() && qv <= pv) {
            add_conflict(c, "p = 2^k - 1 && p & q = 0 && q != 0 => q >= 2^k", { ~C.eq(p, pv), ~C.eq(r), C.eq(q), C.ule(pv + 1, q) });
            return true;
        }

        if (rv != qv) {
            add_conflict(c, "p = 2^k - 1  ==>  (p&q)*2^{N - k} = q*2^{N - k}", { ~C.eq(p, pv), C.eq(r * rational::power_of_two(N - pow), q * rational::power_of_two(N - pow)) });
            return true;
        }

        return false;
    }

}
