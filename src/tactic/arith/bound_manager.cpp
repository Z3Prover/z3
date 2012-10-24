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
#include"bound_manager.h"
#include"ast_smt2_pp.h"
#include"goal.h"

bound_manager::bound_manager(ast_manager & m):
    m_util(m) {
}

bound_manager::~bound_manager() {
    reset();
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

void bound_manager::operator()(expr * f, expr_dependency * d) {
    TRACE("bound_manager", tout << "processing:\n" << mk_ismt2_pp(f, m()) << "\n";);
    expr * v;
    numeral n;
    if (is_disjunctive_bound(f, d))
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
    if (is_uninterp_const(lhs) && m_util.is_numeral(rhs, n, is_int)) {
        v = lhs;
    }
    else if (is_uninterp_const(rhs) && m_util.is_numeral(lhs, n, is_int)) {
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
            m().inc_ref(v);
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
            m().inc_ref(v);
        }
    }
}

bool bound_manager::is_disjunctive_bound(expr * f, expr_dependency * d) {
    numeral lo, hi, n;
    if (!m().is_or(f)) return false;
    unsigned sz = to_app(f)->get_num_args();
    if (sz == 0) return false;
    expr * x, * y, * v = 0;
    bool is_int;
    for (unsigned i = 0; i < sz; ++i) {
        expr * e = to_app(f)->get_arg(i);
        if (!m().is_eq(e, x, y)) return false;
        if (is_uninterp_const(x) && 
            m_util.is_numeral(y, n, is_int) && is_int && 
            (x == v || v == 0)) {
            if (v == 0) { v = x; lo = hi = n; }
            if (n < lo) lo = n;
            if (n > hi) hi = n;
        }
        else if (is_uninterp_const(y) && 
                 m_util.is_numeral(x, n, is_int) && is_int && 
                 (y == v || v == 0)) {
            if (v == 0) { v = y; lo = hi = n; }
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
    unsigned sz = g.size();
    for (unsigned i = 0; i < sz; i++) {
        operator()(g.form(i), g.dep(i));
    }
}

void bound_manager::reset() {
    m().dec_array_ref(m_bounded_vars.size(), m_bounded_vars.c_ptr());
    m_bounded_vars.finalize();
    m_lowers.finalize();
    m_uppers.finalize();
    m_lower_deps.finalize();
    m_upper_deps.finalize();
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
