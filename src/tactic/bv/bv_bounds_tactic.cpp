/*++
Copyright (c) 2016 Microsoft Corporation

Module Name:

    bv_bounds_tactic.cpp

Abstract:

    Contextual bounds simplification tactic.

Author:

    Nikolaj Bjorner (nbjorner) 2016-2-12


--*/

#include "bv_bounds_tactic.h"
#include "ctx_simplify_tactic.h"
#include "bv_decl_plugin.h"
#include "ast_pp.h"

static rational uMaxInt(unsigned sz) {
    return rational::power_of_two(sz) - rational::one();
}

namespace {

struct interval {
    // l < h: [l, h]
    // l > h: [0, h] U [l, UMAX_INT]
    rational l, h;
    unsigned sz;
    bool tight;

    explicit interval() : l(0), h(0), sz(0), tight(false) {}
    interval(const rational& l, const rational& h, unsigned sz, bool tight = false) : l(l), h(h), sz(sz), tight(tight) {
        // canonicalize full set
        if (is_wrapped() && l == h + rational::one()) {
            this->l = rational::zero();
            this->h = uMaxInt(sz);
        }
        SASSERT(invariant());
    }

    bool invariant() const {
        return !l.is_neg() && !h.is_neg() && l <= uMaxInt(sz) && h <= uMaxInt(sz) &&
               (!is_wrapped() || l != h+rational::one());
    }

    bool is_full() const { return l.is_zero() && h == uMaxInt(sz); }
    bool is_wrapped() const { return l > h; }

    bool operator==(const interval& b) const {
        SASSERT(sz == b.sz);
        return l == b.l && h == b.h;
    }
    bool operator!=(const interval& b) const { return !(*this == b); }

    bool implies(const interval& b) const {
        if (b.is_full())
            return true;
        if (is_full())
            return false;

        if (is_wrapped()) {
            // l >= b.l >= b.h >= h
            return b.is_wrapped() && h <= b.h && l >= b.l;
        } else if (b.is_wrapped()) {
            // b.l > b.h >= h >= l
            // h >= l >= b.l > b.h
            return h <= b.h || l >= b.l;
        } else {
            // 
            return l >= b.l && h <= b.h;
        }
    }

    /// return false if intersection is unsat
    bool intersect(const interval& b, interval& result) const {
        if (is_full() || (l == b.l && h == b.h)) {
            result = b;
            return true;
        }
        if (b.is_full()) {
            result = *this;
            return true;
        }

        if (is_wrapped()) {
            if (b.is_wrapped()) {
                if (h >= b.l) {
                    result = b;
                } else if (b.h >= l) {
                    result = *this;
                } else {
                    result = interval(std::max(l, b.l), std::min(h, b.h), sz);
                }
            } else {
                return b.intersect(*this, result);
            }
        } else if (b.is_wrapped()) {
            // ... b.h ... l ... h ... b.l ..
            if (h < b.l && l > b.h) {
                return false;
            }
            // ... l ... b.l ... h ...
            if (h >= b.l && l <= b.h) {
                result = b;
            } else if (h >= b.l) {
                result = interval(b.l, h, sz);
            } else {
                // ... l .. b.h .. h .. b.l ...
                SASSERT(l <= b.h);
                result = interval(l, std::min(h, b.h), sz);
            }
        } else {
            if (l > b.h || h < b.l)
                return false;

            // 0 .. l.. l' ... h ... h'
            result = interval(std::max(l, b.l), std::min(h, b.h), sz, tight && b.tight);
        }
        return true;
    }

    /// return false if negation is empty
    bool negate(interval& result) const {
        if (!tight) {
            result = interval(rational::zero(), uMaxInt(sz), true);
            return true;
        }

        if (is_full())
            return false;
        if (l.is_zero()) {
            result = interval(h + rational::one(), uMaxInt(sz), sz);
        } else if (uMaxInt(sz) == h) {
            result = interval(rational::zero(), l - rational::one(), sz);
        } else {
            result = interval(h + rational::one(), l - rational::one(), sz);
        }
        return true;
    }
};

std::ostream& operator<<(std::ostream& o, const interval& I) {
    o << "[" << I.l << ", " << I.h << "]";
    return o;
}


class bv_bounds_simplifier : public ctx_simplify_tactic::simplifier {
    typedef obj_map<expr, interval> map;

    ast_manager& m;
    bv_util      m_bv;
    vector<map>  m_scopes;
    map         *m_bound;

    bool is_bound(expr *e, expr*& v, interval& b) {
        rational n;
        expr *lhs, *rhs;
        unsigned sz;

        if (m_bv.is_bv_ule(e, lhs, rhs)) {
            if (m_bv.is_numeral(lhs, n, sz)) { // C ule x <=> x uge C
                if (m_bv.is_numeral(rhs))
                    return false;
                b = interval(n, uMaxInt(sz), sz, true);
                v = rhs;
                return true;
            }
            if (m_bv.is_numeral(rhs, n, sz)) { // x ule C
                b = interval(rational::zero(), n, sz, true);
                v = lhs;
                return true;
            }
        } else if (m_bv.is_bv_sle(e, lhs, rhs)) {
            if (m_bv.is_numeral(lhs, n, sz)) { // C sle x <=> x sge C
                if (m_bv.is_numeral(rhs))
                    return false;
                b = interval(n, rational::power_of_two(sz-1) - rational::one(), sz, true);
                v = rhs;
                return true;
            }
            if (m_bv.is_numeral(rhs, n, sz)) { // x sle C
                b = interval(rational::power_of_two(sz-1), n, sz, true);
                v = lhs;
                return true;
            }
        } else if (m.is_eq(e, lhs, rhs)) {
            if (m_bv.is_numeral(lhs, n, sz)) {
                if (m_bv.is_numeral(rhs))
                    return false;
                b = interval(n, n, sz, true);
                v = rhs;
                return true;
            }
            if (m_bv.is_numeral(rhs, n, sz)) {
                b = interval(n, n, sz, true);
                v = lhs;
                return true;
            }
        }
        return false;
    }

public:

    bv_bounds_simplifier(ast_manager& m) : m(m), m_bv(m) {
        m_scopes.push_back(map());
        m_bound = &m_scopes.back();
    }

    virtual ~bv_bounds_simplifier() {}

    virtual bool assert_expr(expr * t, bool sign) {
        while (m.is_not(t, t)) {
            sign = !sign;
        }

        interval b;
        expr* t1;
        if (is_bound(t, t1, b)) {
            SASSERT(!m_bv.is_numeral(t1));
            if (sign)
                VERIFY(b.negate(b));

            push();
            TRACE("bv", tout << (sign?"(not ":"") << mk_pp(t, m) << (sign ? ")" : "") << ": " << mk_pp(t1, m) << " in " << b << "\n";);
            interval& r = m_bound->insert_if_not_there2(t1, b)->get_data().m_value;
            return r.intersect(b, r);
        }
        return true;
    }

    virtual bool simplify(expr* t, expr_ref& result) {
        expr* t1;
        interval b, ctx, intr;
        result = 0;
        bool sign = false;

        while (m.is_not(t, t)) {
            sign = !sign;
        }

        if (!is_bound(t, t1, b))
            return false;

        if (sign && b.tight) {
            sign = false;
            if (!b.negate(b)) {
                result = m.mk_false();
                return true;
            }
        }

        if (m_bound->find(t1, ctx)) {
            if (ctx.implies(b)) {
                result = m.mk_true();
            } else if (!b.intersect(ctx, intr)) {
                result = m.mk_false();
            } else if (intr.l == intr.h) {
                result = m.mk_eq(t1, m_bv.mk_numeral(intr.l, m.get_sort(t1)));
            }
        } else if (b.is_full() && b.tight) {
            result = m.mk_true();
        }

        CTRACE("bv", result != 0, tout << mk_pp(t, m) << " " << b << " (ctx: " << ctx << ") (intr: " << intr << "): " << result << "\n";);
        if (sign && result != 0)
            result = m.mk_not(result);
        return result != 0;
    }

    virtual void push() {
        TRACE("bv", tout << "push\n";);
        unsigned sz = m_scopes.size();
        m_scopes.resize(sz + 1);
        m_bound = &m_scopes.back();
        m_bound->~map();
        new (m_bound) map(m_scopes[sz - 1]);
    }

    virtual void pop(unsigned num_scopes) {
        TRACE("bv", tout << "pop: " << num_scopes << "\n";);
        m_scopes.shrink(m_scopes.size() - num_scopes);
        m_bound = &m_scopes.back();
    }

    virtual simplifier * translate(ast_manager & m) {
        return alloc(bv_bounds_simplifier, m);
    }

    virtual unsigned scope_level() const {
        return m_scopes.size() - 1;
    }
};

}

tactic * mk_bv_bounds_tactic(ast_manager & m, params_ref const & p) {
    return clean(alloc(ctx_simplify_tactic, m, alloc(bv_bounds_simplifier, m), p));
}
