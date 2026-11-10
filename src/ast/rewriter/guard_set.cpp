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
#include "ast/datatype_decl_plugin.h"
#include <algorithm>
#include <limits>

seq::predicate_algebra::predicate_algebra(ast_manager& _m, seq_util& _u, sort* elem_sort, expr* v0,
                                          cache* cache)
    : m(_m), u(_u), m_sort(elem_sort), m_v0(v0),
      m_is_char(_u.is_char(elem_sort)), m_rp_cache(cache) {
    SASSERT(v0->get_sort() == elem_sort);
}

void seq::predicate_algebra::cache::reset() {
    for (auto const& [k, v] : m_cache) dealloc(v);
    m_cache.reset();
    dealloc(m_fresh);
    m_trail.reset();
    m_fresh = nullptr;
}

seq::range_predicate* seq::predicate_algebra::cache::fresh(unsigned max_char) {
    if (!m_fresh) m_fresh = alloc(seq::range_predicate, max_char);
    return m_fresh;
}

void seq::predicate_algebra::cache::insert(expr* g, seq::range_predicate* p) {
    if (p) m_fresh = nullptr;  // ownership transferred to map
    m_trail.push_back(g);
    m_cache.insert(g, p);
}

void seq::predicate_algebra::collect_consts(expr* g, ptr_vector<expr>& out) const {
    expr* a = nullptr, * b = nullptr;
    if (m.is_and(g) || m.is_or(g)) {
        for (expr* arg : *to_app(g)) collect_consts(arg, out);
        return;
    }
    if (m.is_not(g, a)) { collect_consts(a, out); return; }
    if (m.is_eq(g, a, b)) {
        if (m.is_bool(a)) {
            collect_consts(a, out);
            collect_consts(b, out);
            return;
        }
        if (a == m_v0 && is_ground(b)) out.push_back(b);
        else if (b == m_v0 && is_ground(a)) out.push_back(a);
    }
}

lbool seq::predicate_algebra::eval_at(expr* g, expr* cand) const {
    expr* a = nullptr, * b = nullptr;
    if (m.is_true(g))  return l_true;
    if (m.is_false(g)) return l_false;
    if (g == m_v0 && m.is_bool(m_sort))
        return m.is_true(cand) ? l_true : m.is_false(cand) ? l_false : l_undef;
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
        if (a == b) return l_true;
        if (m.is_bool(a)) {
            lbool lhs = eval_at(a, cand), rhs = eval_at(b, cand);
            return lhs == l_undef || rhs == l_undef ? l_undef : lhs == rhs ? l_true : l_false;
        }
        expr* other = (a == m_v0) ? b : (b == m_v0 ? a : nullptr);
        if (other) {
            if (!is_ground(other)) return l_undef;
            a = cand;
            b = other;
        }
        else if (!is_ground(a) || !is_ground(b))
            return l_undef;
        return m.are_equal(a, b) ? l_true : m.are_distinct(a, b) ? l_false : l_undef;
    }
    return l_undef;
}

lbool seq::predicate_algebra::mk_fresh(ptr_vector<expr> const& consts, expr_ref& out) const {
    arith_util a(m);
    if (a.is_int_real(m_sort)) {
        rational mx(0); bool any = false;
        for (expr* c : consts) {
            rational v;
            if (a.is_numeral(c, v)) { if (!any || v > mx) mx = v; any = true; }
        }
        out = a.mk_numeral(any ? mx + rational(1) : rational(0), a.is_int(m_sort));
        return l_true;
    }
    bv_util bv(m);
    if (bv.is_bv_sort(m_sort)) {
        unsigned sz = bv.get_bv_size(m_sort);
        for (unsigned k = 0; k <= consts.size(); ++k) {
            if (sz < std::numeric_limits<unsigned>::digits && k == (1u << sz))
                return l_false;
            rational kv(k);
            bool clash = false;
            for (expr* c : consts) {
                rational v; unsigned bsz = 0;
                if (bv.is_numeral(c, v, bsz) && v == kv) { clash = true; break; }
            }
            if (!clash) { out = bv.mk_numeral(kv, sz); return l_true; }
        }
        UNREACHABLE();
    }
    return l_undef;
}

lbool seq::predicate_algebra::generic_eval(expr* g, expr_ref* witness) const {
    if (m.is_false(g))
        return l_false;
    bool saw_undef = false;
    auto test = [&](expr* c) {
        lbool r = eval_at(g, c);
        if (r == l_true && witness) *witness = c;
        if (r == l_undef) saw_undef = true;
        return r == l_true;
    };
    if (m.is_bool(m_sort)) {
        if (test(m.mk_false()) || test(m.mk_true()))
            return l_true;
        return saw_undef ? l_undef : l_false;
    }
    datatype_util dt(m);
    if (dt.is_enum_sort(m_sort)) {
        for (func_decl* c : *dt.get_datatype_constructors(m_sort)) {
            if (!m.inc()) return l_undef;
            expr_ref value(m.mk_const(c), m);
            if (test(value)) return l_true;
        }
        return saw_undef ? l_undef : l_false;
    }
    ptr_vector<expr> consts;
    collect_consts(g, consts);
    for (expr* c : consts) {
        if (!m.is_value(c)) saw_undef = true;
        if (test(c)) return l_true;
    }
    expr_ref fresh(m);
    lbool remaining = mk_fresh(consts, fresh);
    if (remaining == l_true && test(fresh))
        return l_true;
    if (remaining == l_undef)
        saw_undef = true;
    return saw_undef ? l_undef : l_false;
}

bool seq::predicate_algebra::conjoin_ranges(expr* g, range_predicate& accumulated) const {
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
        if (!s) return false;
        accumulated = accumulated & *s;
        return true;
    }
    seq::range_predicate s(u.max_char());
    if (seq::guard_to_range_predicate(u, m_v0, g, s)) 
        accumulated = accumulated & s;
    else
        return false;
    return true;
}

lbool seq::predicate_algebra::eval(expr* g, expr_ref* witness) const {
    if (!m_is_char)
        return generic_eval(g, witness);
    range_predicate ranges = range_predicate::top(u.max_char());
    if (!conjoin_ranges(g, ranges)) return l_undef;
    if (ranges.is_empty()) return l_false;
    if (witness) *witness = u.mk_char(ranges[0].first);
    return l_true;
}

expr_ref seq::predicate_algebra::from_ranges(range_predicate const& ranges) const {
    if (ranges.is_empty()) return mk_bottom();
    if (ranges.is_top()) return mk_top();
    range_predicate neg = ~ranges;
    bool complement = neg.num_ranges() < ranges.num_ranges();
    auto const& selected = complement ? neg : ranges;
    expr_ref_vector disjuncts(m);
    for (auto [lo, hi] : selected.ranges()) {
        expr_ref lower(u.mk_char(lo), m), upper(u.mk_char(hi), m);
        expr_ref term(m);
        if (lo == hi)
            term = m.mk_eq(m_v0, lower);
        else if (lo == 0)
            term = u.mk_le(m_v0, upper);
        else if (hi == u.max_char())
            term = u.mk_le(lower, m_v0);
        else {
            expr_ref lhs(u.mk_le(lower, m_v0), m), rhs(u.mk_le(m_v0, upper), m);
            term = m.mk_and(lhs, rhs);
        }
        disjuncts.push_back(term);
    }
    expr_ref result(disjuncts.size() == 1 ? disjuncts.get(0) :
                    m.mk_or(disjuncts.size(), disjuncts.data()), m);
    if (complement) result = m.mk_not(result);
    return result;
}

expr_ref seq::predicate_algebra::from_values(expr_ref_vector const& values, bool complement) const {
    expr_ref_vector atoms(m);
    for (expr* value : values)
        atoms.push_back(m.mk_eq(m_v0, value));
    expr_ref result(atoms.empty() ? m.mk_false() : atoms.size() == 1 ? atoms.get(0) :
                    m.mk_or(atoms.size(), atoms.data()), m);
    if (complement)
        result = atoms.empty() ? m.mk_true() : m.mk_not(result);
    return result;
}

expr_ref seq::predicate_algebra::normalize(expr* predicate) const {
    expr_ref g(predicate, m);
    if (m.is_true(g) || m.is_false(g))
        return g;
    if (m_is_char) {
        range_predicate ranges = range_predicate::top(u.max_char());
        return conjoin_ranges(g, ranges) ? from_ranges(ranges) : g;
    }
    if (m.is_bool(m_sort)) {
        lbool f = eval_at(g, m.mk_false()), t = eval_at(g, m.mk_true());
        if (f == l_undef || t == l_undef) return g;
        if (f == t) return f == l_true ? mk_top() : mk_bottom();
        return expr_ref(t == l_true ? m_v0 : m.mk_not(m_v0), m);
    }
    datatype_util dt(m);
    if (dt.is_enum_sort(m_sort)) {
        expr_ref_vector values(m);
        auto const& constructors = *dt.get_datatype_constructors(m_sort);
        for (func_decl* c : constructors) {
            if (!m.inc()) return g;
            expr_ref value(m.mk_const(c), m);
            lbool r = eval_at(g, value);
            if (r == l_undef) return g;
            if (r == l_true) values.push_back(value);
        }
        return values.size() == constructors.size() ? mk_top() : from_values(values, false);
    }
    bv_util bv(m);
    arith_util ar(m);
    bool is_bv = bv.is_bv_sort(m_sort);
    if (!is_bv && !ar.is_int_real(m_sort))
        return g;
    ptr_vector<expr> consts;
    collect_consts(g, consts);
    if (!consts.empty()) {
        std::sort(consts.begin(), consts.end(), less);
        consts.shrink(static_cast<unsigned>(std::unique(consts.begin(), consts.end()) - consts.begin()));
    }
    expr_ref_vector accepted(m), rejected(m);
    for (expr* c : consts) {
        if (!m.inc()) return g;
        if (is_bv ? !bv.is_numeral(c) : !ar.is_numeral(c))
            return g;
        lbool r = eval_at(g, c);
        if (r == l_undef) return g;
        (r == l_true ? accepted : rejected).push_back(c);
    }
    expr_ref fresh(m);
    lbool remaining = mk_fresh(consts, fresh);
    if (remaining == l_undef) return g;
    lbool default_value = remaining == l_true ? eval_at(g, fresh) : l_false;
    if (default_value == l_undef) return g;
    bool complement = default_value == l_true;
    uint64_t domain = 0;
    if (is_bv && bv.get_bv_size(m_sort) <= 32) {
        domain = uint64_t(1) << bv.get_bv_size(m_sort);
        uint64_t count = accepted.size() + (complement ? domain - consts.size() : 0);
        complement = count > domain / 2;
    }
    expr_ref_vector values(m);
    values.append(complement ? rejected : accepted);
    if (remaining == l_true && complement != (default_value == l_true)) {
        // Changing polarity only occurs when at least half a small BV domain
        // was mentioned, so this enumeration is bounded by the input size.
        SASSERT(domain && domain <= 2ull * consts.size());
        obj_hashtable<expr> mentioned;
        for (expr* c : consts) mentioned.insert(c);
        for (uint64_t i = 0; i < domain; ++i) {
            if (!m.inc()) return g;
            expr_ref value(bv.mk_numeral(rational(i, rational::ui64()), bv.get_bv_size(m_sort)), m);
            if (!mentioned.contains(value))
                values.push_back(value);
        }
    }
    if (!values.empty())
        std::sort(values.data(), values.data() + values.size(), less);
    return from_values(values, complement);
}

expr_ref seq::predicate_algebra::mk_and(expr* a, expr* b) const {
    expr_ref g(m.mk_and(a, b), m);
    return normalize(g);
}

expr_ref seq::predicate_algebra::mk_or(expr* a, expr* b) const {
    expr_ref g(m.mk_or(a, b), m);
    return normalize(g);
}

expr_ref seq::predicate_algebra::mk_not(expr* a) const {
    expr_ref g(m.mk_not(a), m);
    return normalize(g);
}

guard_set::guard_set(ast_manager& m, seq_util& u, sort* elem_sort, expr* v0, cache* cache)
    : m_algebra(m, u, elem_sort, v0, cache), m_is_char(u.is_char(elem_sort)),
      m_rp(u.max_char()), m_guard(m) {
    if (m_is_char) m_rp = seq::range_predicate::top(u.max_char());
    else m_guard = m_algebra.mk_top();
}

void guard_set::conjoin(expr* g) {
    if (!m_ok) return;
    if (m_is_char)
        m_ok = m_algebra.conjoin_ranges(g, m_rp);
    else
        m_guard = m_algebra.mk_and(m_guard, g);
}

lbool guard_set::eval(expr_ref* witness) const {
    if (!m_ok) return l_undef;
    if (m_is_char) {
        if (m_rp.is_empty()) return l_false;
        if (witness) *witness = m_algebra.u.mk_char(m_rp[0].first);
        return l_true;
    }
    return m_algebra.eval(m_guard, witness);
}
