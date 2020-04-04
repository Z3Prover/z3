/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    bound_manager.cpp

Abstract:

    Collect bounds.

Author:

    Leonardo (leonardo) 2011-05-16

Notes:

--*/
#include "tactic/arith/bound_manager.h"
#include "ast/ast_smt2_pp.h"
#include "ast/ast_pp.h"
#include "tactic/goal.h"

bound_manager::bound_manager(ast_manager & m):
    m_util(m),
    m_bounded_vars(m) {
}

bound_manager::~bound_manager() {
    reset();
}

bound_manager* bound_manager::translate(ast_manager& dst_m) {
    bound_manager* result = alloc(bound_manager, dst_m);
    ast_translation tr(m(), dst_m);
    expr_dependency_translation edtr(tr);
    for (auto& kv : m_lowers) result->m_lowers.insert(tr(kv.m_key), kv.m_value);
    for (auto& kv : m_uppers) result->m_uppers.insert(tr(kv.m_key), kv.m_value);
    for (auto& kv : m_lower_deps) result->m_lower_deps.insert(tr(kv.m_key), edtr(kv.m_value));
    for (auto& kv : m_upper_deps) result->m_upper_deps.insert(tr(kv.m_key), edtr(kv.m_value));
    for (expr* e : m_bounded_vars) result->m_bounded_vars.push_back(tr(e));
    return result;
}


static decl_kind swap_decl(decl_kind k) {
    switch (k) {
    case OP_LE: return OP_GE;
    case OP_LT: return OP_GT;
    case OP_GE: return OP_LE;
    case OP_GT: return OP_LT;
    default:
        UNREACHABLE();
        return k;
    }
}

decl_kind bound_manager::neg(decl_kind k) {
    switch (k) {
    case OP_LE: return OP_GT;
    case OP_LT: return OP_GE;
    case OP_GE: return OP_LT;
    case OP_GT: return OP_LE;
    default:
        UNREACHABLE();
        return k;
    }
}

void bound_manager::norm(numeral & n, decl_kind & k) {
    switch (k) {
    case OP_LE: return;
    case OP_GE: return;
    case OP_LT: 
        // x < n --> x <= n-1
        n--;
        k = OP_LE;
        return;
    case OP_GT:
        // x > n --> x >= n+1
        n++;
        k = OP_GE;
        return;
    default:
        return;
    }
}

static bool is_lower(decl_kind k) {
    return k == OP_GT || k == OP_GE;
}

static bool is_strict(decl_kind k) {
    return k == OP_LT || k == OP_GT;
} 

bool bound_manager::is_numeral(expr* v, numeral& n, bool& is_int) {
    expr* w;
    if (m_util.is_uminus(v, w) && is_numeral(w, n, is_int)) {
        n.neg();
        return true;
    }
    return m_util.is_numeral(v, n, is_int);
}

void bound_manager::operator()(expr * f, expr_dependency * d) {
    TRACE("bound_manager", tout << "processing:\n" << mk_ismt2_pp(f, m()) << "\n";);
    expr * v;
    numeral n;
    if (is_disjunctive_bound(f, d))
        return;
    if (is_equality_bound(f, d))
        return;
    bool pos = true;    
    while (m().is_not(f, f))
        pos = !pos;
    if (!is_app(f))
        return;
    app * t = to_app(f);
    if (t->get_family_id() != m_util.get_family_id())
        return;
    decl_kind k = t->get_decl_kind();
    if (k != OP_LE && k != OP_GE && k != OP_LT && k != OP_GT)
        return;
    expr * lhs = t->get_arg(0);
    expr * rhs = t->get_arg(1);
    bool is_int;
    if (is_uninterp_const(lhs) && is_numeral(rhs, n, is_int)) {
        v = lhs;
    }
    else if (is_uninterp_const(rhs) && is_numeral(lhs, n, is_int)) {
        v = rhs;
        k = swap_decl(k);
    }
    else {
        return;
    }
    if (!pos)
        k = neg(k);
    if (is_int)
        norm(n, k);
    TRACE("bound_manager", tout << "found bound for:\n" << mk_ismt2_pp(v, m()) << "\n";);
    bool strict = is_strict(k);
    if (is_lower(k)) {
        insert_lower(v, strict, n, d);
    }
    else {
        insert_upper(v, strict, n, d);
    }
}

void bound_manager::insert_upper(expr * v, bool strict, numeral const & n, expr_dependency * d) {
    limit old;
    if (m_uppers.find(v, old)) {
        if (n < old.first || (n == old.first && strict && !old.second)) {
            // improved bound
            m_uppers.insert(v, limit(n, strict));
            if (d)
                m_upper_deps.insert(v, d);
        }
    }
    else {
        m_uppers.insert(v, limit(n, strict));
        if (d)
            m_upper_deps.insert(v, d);
        if (!m_lowers.contains(v)) {
            m_bounded_vars.push_back(v);
        }
    }
}

void bound_manager::insert_lower(expr * v, bool strict, numeral const & n, expr_dependency * d) {
    limit old;
    if (m_lowers.find(v, old)) {
        if (n > old.first || (n == old.first && strict && !old.second)) {
            // improved bound
            m_lowers.insert(v, limit(n, strict));
            if (d)
                m_lower_deps.insert(v, d);
        }
    }
    else {
        m_lowers.insert(v, limit(n, strict));
        if (d)
            m_lower_deps.insert(v, d);
        if (!m_uppers.contains(v)) {
            m_bounded_vars.push_back(v);
        }
    }
}

bool bound_manager::is_equality_bound(expr * f, expr_dependency * d) {
    expr* x, *y;
    if (!m().is_eq(f, x, y)) {
        return false;
    }
    if (!is_uninterp_const(x)) {
        std::swap(x, y);
    }
    numeral n;
    bool is_int;
    if (is_uninterp_const(x) && is_numeral(y, n, is_int)) {
        insert_lower(x, false, n, d);
        insert_upper(x, false, n, d);
        return true;
    }
    else {
        return false;
    }
}

bool bound_manager::is_disjunctive_bound(expr * f, expr_dependency * d) {
    numeral lo, hi, n;
    if (!m().is_or(f)) return false;
    unsigned sz = to_app(f)->get_num_args();
    if (sz == 0) return false;
    expr * x, * y, * v = nullptr;
    bool is_int;
    for (unsigned i = 0; i < sz; ++i) {
        expr * e = to_app(f)->get_arg(i);
        if (!m().is_eq(e, x, y)) return false;
        if (is_uninterp_const(x) && 
            is_numeral(y, n, is_int) && is_int && 
            (x == v || v == nullptr)) {
            if (v == nullptr) { v = x; lo = hi = n; }
            if (n < lo) lo = n;
            if (n > hi) hi = n;
        }
        else if (is_uninterp_const(y) && 
                 is_numeral(x, n, is_int) && is_int && 
                 (y == v || v == nullptr)) {
            if (v == nullptr) { v = y; lo = hi = n; }
            if (n < lo) lo = n;
            if (n > hi) hi = n;
        }
        else {
            return false;
        }
    }
    TRACE("bound_manager", tout << "bounds: " << lo << " " << hi << "\n";);
    insert_lower(v, false, lo, d);
    insert_upper(v, false, hi, d);
    return true;
}

void bound_manager::operator()(goal const & g) {
    if (g.proofs_enabled())
        return;
    unsigned sz = g.size();
    for (unsigned i = 0; i < sz; i++) {
        operator()(g.form(i), g.dep(i));
    }
}


void bound_manager::reset() {
    m_bounded_vars.finalize();
    m_lowers.finalize();
    m_uppers.finalize();
    m_lower_deps.finalize();
    m_upper_deps.finalize();
}

bool bound_manager::inconsistent() const {
    for (auto const& kv : m_lowers) {
        limit const& lim1 = kv.m_value;
        limit lim2;        
        if (m_uppers.find(kv.m_key, lim2)) {
            if (lim1.first > lim2.first) {
                return true;
            }
            if (lim1.first == lim2.first &&
                !lim1.second && lim2.second) {
                return true;
            }
        }
    }
    return false;
}

void bound_manager::display(std::ostream & out) const {
    numeral n; bool strict;
    for (iterator it = begin(); it != end(); ++it) {
        expr * v = *it;
        if (has_lower(v, n, strict))
            out << n << " " << (strict ? "<" : "<=");
        else
            out << "-oo <";
        out << " " << mk_ismt2_pp(v, m()) << " ";
        if (has_upper(v, n, strict))
            out << (strict ? "<" : "<=") << " " << n;
        else
            out << "< oo";
        out << "\n";
    }
}
