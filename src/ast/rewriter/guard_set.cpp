/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    guard_set.cpp

Abstract:

    Implementation of guard_set.  See guard_set.h.

Author:

    Nikolaj Bjorner / Margus Veanes 2026

--*/

#include "ast/rewriter/guard_set.h"
#include "ast/arith_decl_plugin.h"
#include "ast/bv_decl_plugin.h"

guard_set::guard_set(ast_manager& _m, seq_util& _u, sort* elem_sort, expr* v0,
                     guard_set::cache* cache)
    : m(_m), u(_u), m_sort(elem_sort), m_v0(v0),
      m_is_char(_u.is_char(elem_sort)), m_rp_cache(cache),
      m_rp(_u.max_char()), m_guard(_m) {
    if (m_is_char) m_rp = seq::range_predicate::top(u.max_char());
    else           m_guard = m.mk_true();
}

void guard_set::cache::reset() {
    for (auto const& [k, v] : m_cache) dealloc(v);
    m_cache.reset();
    dealloc(m_fresh);
    m_trail.reset();
    m_fresh = nullptr;
}

seq::range_predicate* guard_set::cache::fresh(unsigned max_char) {
    if (!m_fresh) m_fresh = alloc(seq::range_predicate, max_char);
    return m_fresh;
}

void guard_set::cache::insert(expr* g, seq::range_predicate* p) {
    if (p) m_fresh = nullptr;  // ownership transferred to map
    m_trail.push_back(g);
    m_cache.insert(g, p);
}

void guard_set::collect_consts(expr* g, ptr_vector<expr>& out) const {
    expr* a = nullptr, * b = nullptr;
    if (m.is_and(g) || m.is_or(g)) {
        for (expr* arg : *to_app(g)) collect_consts(arg, out);
        return;
    }
    if (m.is_not(g, a)) { collect_consts(a, out); return; }
    if (m.is_eq(g, a, b)) {
        if (a == m_v0 && b != m_v0) out.push_back(b);
        else if (b == m_v0 && a != m_v0) out.push_back(a);
    }
}

lbool guard_set::eval_at(expr* g, expr* cand) const {
    expr* a = nullptr, * b = nullptr;
    if (m.is_true(g))  return l_true;
    if (m.is_false(g)) return l_false;
    if (m.is_not(g, a)) {
        lbool r = eval_at(a, cand);
        return r == l_undef ? l_undef : (r == l_true ? l_false : l_true);
    }
    if (m.is_and(g)) {
        lbool r = l_true;
        for (expr* arg : *to_app(g)) {
            lbool e = eval_at(arg, cand);
            if (e == l_false) return l_false;
            if (e == l_undef) r = l_undef;
        }
        return r;
    }
    if (m.is_or(g)) {
        lbool r = l_false;
        for (expr* arg : *to_app(g)) {
            lbool e = eval_at(arg, cand);
            if (e == l_true) return l_true;
            if (e == l_undef) r = l_undef;
        }
        return r;
    }
    if (m.is_eq(g, a, b)) {
        expr* other = (a == m_v0) ? b : (b == m_v0 ? a : nullptr);
        if (!other) return l_undef;
        if (other == m_v0) return l_true;
        return (cand == other) ? l_true : l_false;   // canonical values: identity == equality
    }
    return l_undef;
}

bool guard_set::mk_fresh(ptr_vector<expr> const& consts, expr_ref& out) const {
    if (m.is_bool(m_sort)) {
        bool hasT = false, hasF = false;
        for (expr* c : consts) { if (m.is_true(c)) hasT = true; else if (m.is_false(c)) hasF = true; }
        if (!hasT) { out = m.mk_true();  return true; }
        if (!hasF) { out = m.mk_false(); return true; }
        return false;
    }
    arith_util a(m);
    if (a.is_int_real(m_sort)) {
        rational mx(0); bool any = false;
        for (expr* c : consts) {
            rational v;
            if (a.is_numeral(c, v)) { if (!any || v > mx) mx = v; any = true; }
        }
        out = a.mk_numeral(any ? mx + rational(1) : rational(0), a.is_int(m_sort));
        return true;
    }
    bv_util bv(m);
    if (bv.is_bv_sort(m_sort)) {
        unsigned sz = bv.get_bv_size(m_sort);
        for (unsigned k = 0; k <= consts.size(); ++k) {
            rational kv(k);
            bool clash = false;
            for (expr* c : consts) {
                rational v; unsigned bsz = 0;
                if (bv.is_numeral(c, v, bsz) && v == kv) { clash = true; break; }
            }
            if (!clash) { out = bv.mk_numeral(kv, sz); return true; }
        }
        return false;
    }
    return false;
}

lbool guard_set::generic_eval(expr_ref* witness) const {
    ptr_vector<expr> consts;
    collect_consts(m_guard, consts);
    bool saw_undef = false;
    for (expr* c : consts) {
        lbool r = eval_at(m_guard, c);
        if (r == l_true) { if (witness) *witness = expr_ref(c, m); return l_true; }
        if (r == l_undef) saw_undef = true;
    }
    expr_ref fresh(m);
    if (mk_fresh(consts, fresh)) {
        lbool r = eval_at(m_guard, fresh);
        if (r == l_true) { if (witness) *witness = fresh; return l_true; }
        if (r == l_undef) saw_undef = true;
    }
    else
        saw_undef = true;   // the "distinct from all mentioned values" region is untested
    return saw_undef ? l_undef : l_false;
}

void guard_set::conjoin(expr* g) {
    if (!m_ok) 
        return;
    if (!m_is_char) {
        m_guard = m.mk_and(m_guard, g);
        return;
    }
    if (m_rp_cache) {
        // Translating a guard expression into a range predicate is the inner loop of the
        // product-transition enumeration; the same handful of guards recurs on every
        // branch, so translate each one once.
        seq::range_predicate* s = nullptr;
        if (!m_rp_cache->find(g, s)) {
            s = m_rp_cache->fresh(u.max_char());
            if (!seq::guard_to_range_predicate(u, m_v0, g, *s)) 
                s = nullptr; // recycles s into m_fresh
            m_rp_cache->insert(g, s);   
        }
        if (!s) { m_ok = false; return; }
        m_rp = m_rp & *s;
        return;
    }
    seq::range_predicate s(u.max_char());
    if (seq::guard_to_range_predicate(u, m_v0, g, s)) 
        m_rp = m_rp & s;
    else 
        m_ok = false;     
}

lbool guard_set::eval(expr_ref* witness) const {
    if (!m_ok) return l_undef;
    if (m_is_char) {
        if (m_rp.is_empty()) return l_false;
        if (witness) *witness = expr_ref(u.mk_char(m_rp[0].first), m);
        return l_true;
    }
    return generic_eval(witness);
}
