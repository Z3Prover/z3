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
                    bound(!lo, s).insert(t1, n);
                }
            }
            else {
                bound(lo, s).insert(t1, n);                
            }
        }
    }

    virtual bool simplify(expr* t, expr_ref& result) {
        bool lo, s;
        expr* t1;
        rational b1, b2;
        if (is_bound(t, t1, lo, s, b1)) {
            if (bound(!lo, s).find(t1, b2)) {
                // t1 <= b1 < b2 <= t1
                if (lo && b2 > b1) {
                    result = m.mk_false();
                    return true;
                }
                // t1 >= b1 > b2 >= t1
                if (!lo && b2 < b1) {
                    result = m.mk_false();
                    return true;
                }
                if (b1 == b2) {
                    result = m.mk_eq(t1, m_bv.mk_numeral(b1, m.get_sort(t1)));
                    return true;
                }
            }
            if (bound(lo, s).find(t1, b2)) {
                // b1 <= b2 <= t1 
                if (lo && b1 <= b2) {
                    result = m.mk_true();
                    return true;
                }
                // b1 >= b2 >= t1
                if (!lo && b1 >= b2) {
                    result = m.mk_true();
                    return true;
                }
            }
        }
        return false;
    }

    virtual void push() {
        m_scopes.push_back(m_trail.size());
    }

    virtual void pop(unsigned num_scopes) {
        if (num_scopes == 0) return;
        unsigned old_sz = m_scopes[m_scopes.size() - num_scopes];
        for (unsigned i = old_sz; i < m_trail.size(); ++i) {
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

