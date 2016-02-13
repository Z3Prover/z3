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

class bv_bounds_simplifier : public ctx_simplify_tactic::simplifier {
    ast_manager&            m;
    bv_util                 m_bv;
    unsigned_vector         m_scopes;
    expr_ref_vector         m_trail;
    unsigned_vector         m_trail_kind;
    obj_map<expr, rational> m_bound[4];

    obj_map<expr, rational> & sle() { return m_bound[0]; }
    obj_map<expr, rational> & ule() { return m_bound[1]; }
    obj_map<expr, rational> & sge() { return m_bound[2]; }
    obj_map<expr, rational> & uge() { return m_bound[3]; }

    obj_map<expr, rational> & bound(bool lo, bool s) {
        if (lo) {
            if (s) return sle(); return ule();
        }
        else {
            if (s) return sge(); return uge();
        }
    }

    void add_bound(bool lo, bool s, expr* t, rational const& n) {
        push();
        bound(lo, s).insert(t, n);
        m_trail.push_back(t);
        m_trail_kind.push_back(lo?(s?0:1):(s?2:3));
    }

    bool is_bound(expr* t, expr*& b, bool& lo, bool& sign, rational& n) {
        expr* t1, *t2;
        unsigned sz;
        if (m_bv.is_bv_ule(t, t1, t2)) {
            sign = false;
            if (m_bv.is_numeral(t1, n, sz)) {
                lo = true; 
                b  = t2;
                return true;
            }
            else if (m_bv.is_numeral(t2, n, sz)) {
                lo = false;
                b  = t1;
                return true;
            }
        }
        else if (m_bv.is_bv_sle(t, t1, t2)) {
            sign = true;
            if (m_bv.is_numeral(t2, n, sz)) {
                n = m_bv.norm(n, sz, true);
                lo = false;
                b  = t1;
                return true;
            }
            else if (m_bv.is_numeral(t1, n, sz)) {
                n = m_bv.norm(n, sz, true);
                lo = true;
                b  = t2;
                return true;
            }
        }
        return false;
    }

    bool is_eq_const(expr* t, expr*& b, rational& n) {
        expr* t1, *t2;
        unsigned sz;
        if (m.is_eq(t, t1, t2)) {
            if (m_bv.is_numeral(t1, n, sz)) {
                b = t2;
                return true;
            }
            if (m_bv.is_numeral(t2, n, sz)) {
                b = t1;
                return true;
            }
        }
        return false;
    }
    
public:

    bv_bounds_simplifier(ast_manager& m): m(m), m_bv(m), m_trail(m) {}

    virtual ~bv_bounds_simplifier() {}

    virtual void assert_expr(expr * t, bool sign) {
        bool lo, s;
        expr* t1;
        rational n;
        if (is_bound(t, t1, lo, s, n)) {
            if (sign) {
                // !(n <= t1) <=> t1 <= n - 1
                // !(t1 <= n) <=> t1 >= n + 1
                if (lo) {
                    n -= rational::one();
                }
                else {
                    n += rational::one();
                }
                // check overflow conditions:
                rational n1 = m_bv.norm(n, m_bv.get_bv_size(t1), s);
                if (n1 == n) {
                    TRACE("bv", tout << "(not " << mk_pp(t, m) << "): " << mk_pp(t1, m) << (lo?" <= ":" >= ") << n << "\n";);
                    add_bound(!lo, s, t1, n);
                }
            }
            else {
                TRACE("bv", tout << mk_pp(t, m) << ": " << mk_pp(t1, m) << (lo?" >= ":" <= ") << n << "\n";);
                add_bound(lo, s, t1, n);
            }
        }
    }

    virtual bool simplify(expr* t, expr_ref& result) {
        bool lo, s;
        expr* t1;
        rational b1, b2;
        result = 0;
        if (is_bound(t, t1, lo, s, b1)) {
            if (bound(!lo, s).find(t1, b2)) {
                // t1 >= b1 > b2 >= t1
                if (lo && b1 > b2) {
                    result = m.mk_false();
                }
                // t1 <= b1 < b2 <= t1
                else if (!lo && b1 < b2) {
                    result = m.mk_false();
                }
                else if (b1 == b2) {
                    result = m.mk_eq(t1, m_bv.mk_numeral(b1, m.get_sort(t1)));
                }
            }
            if (result == 0 && bound(lo, s).find(t1, b2)) {
                // b1 <= b2 <= t1 
                if (lo && b1 <= b2) {
                    result = m.mk_true();
                }
                // b1 >= b2 >= t1
                else if (!lo && b1 >= b2) {
                    result = m.mk_true();
                }
            }
        }
        if (is_eq_const(t, t1, b1)) {
            if (bound(true, false).find(t1, b2) && b2 > b1) {
                result = m.mk_false();
            }
            else if (bound(false, false).find(t1, b2) && b2 < b1) {
                result = m.mk_false();
            }
            else {
                if (bound(true, true).find(t1, b2)) {
                    b1 = m_bv.norm(b1, m_bv.get_bv_size(t1), true);
                    if (b2 > b1) result = m.mk_false();
                }
                if (result == 0 && bound(false, true).find(t1, b2)) {
                    b1 = m_bv.norm(b1, m_bv.get_bv_size(t1), true);
                    if (b2 < b1) result = m.mk_false();
                }
            }
        }
        CTRACE("bv", result != 0, tout << mk_pp(t, m) << " " << (lo?"lo":"hi") << " " << b1 << " " << b2 << ": " << result << "\n";);
        return result != 0;
    }

    virtual void push() {
        TRACE("bv", tout << "push\n";);
        m_scopes.push_back(m_trail.size());
    }

    virtual void pop(unsigned num_scopes) {
        TRACE("bv", tout << "pop: " << num_scopes << "\n";);
        if (num_scopes == 0) return;
        unsigned old_sz = m_scopes[m_scopes.size() - num_scopes];
        for (unsigned i = old_sz; i < m_trail.size(); ++i) {
            TRACE("bv", tout << "remove: " << mk_pp(m_trail[i].get(), m) << "\n";);
            SASSERT(m_bound[m_trail_kind[i]].contains(m_trail[i].get()));
            m_bound[m_trail_kind[i]].erase(m_trail[i].get());
        }
        m_trail_kind.resize(old_sz);
        m_trail.resize(old_sz);
        m_scopes.shrink(m_scopes.size() - num_scopes);
    }

    virtual simplifier * translate(ast_manager & m) {
        return alloc(bv_bounds_simplifier, m);
    }

    virtual unsigned scope_level() const {
        return m_scopes.size();
    }
    
};

tactic * mk_bv_bounds_tactic(ast_manager & m, params_ref const & p) {
    return clean(alloc(ctx_simplify_tactic, m, alloc(bv_bounds_simplifier, m), p));
}

