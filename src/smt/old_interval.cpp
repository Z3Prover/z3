/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    old_interval.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-12-09.

Revision History:

--*/

#include"old_interval.h"

void ext_numeral::neg() {
    switch (m_kind) {
    case MINUS_INFINITY: m_kind = PLUS_INFINITY; break;
    case FINITE:         m_value.neg(); break;
    case PLUS_INFINITY:  m_kind = MINUS_INFINITY; break;
    }
}

ext_numeral & ext_numeral::operator+=(ext_numeral const & other) {
    SASSERT(!is_infinite() || !other.is_infinite() || m_kind == other.m_kind);
    if (is_infinite())
        return *this;
    SASSERT(m_kind == FINITE);
    switch (other.m_kind) {
    case MINUS_INFINITY:
        m_kind = MINUS_INFINITY;
        m_value.reset();
        return *this;
    case FINITE:
        m_value += other.m_value;
        return *this;
    case PLUS_INFINITY:
        m_kind = PLUS_INFINITY;
        m_value.reset();
        return *this;
    }
    UNREACHABLE();
    return *this;
}

ext_numeral & ext_numeral::operator-=(ext_numeral const & other) {
    SASSERT(!is_infinite() || !other.is_infinite() || (m_kind != other.m_kind));
    if (is_infinite())
        return *this;
    SASSERT(m_kind == FINITE);
    switch (other.m_kind) {
    case MINUS_INFINITY:
        m_kind = PLUS_INFINITY;
        m_value.reset();
        return *this;
    case FINITE:
        m_value -= other.m_value;
        return *this;
    case PLUS_INFINITY:
        m_kind = MINUS_INFINITY;
        m_value.reset();
        return *this;
    }
    UNREACHABLE();
    return *this;
}

ext_numeral & ext_numeral::operator*=(ext_numeral const & other) {
    if (is_zero()) {
        m_kind = FINITE;
        return *this;
    }
    if (other.is_zero()) {
        m_kind = FINITE;
        m_value.reset();
        return *this;
    }
    
    if (is_infinite() || other.is_infinite()) {
        if (sign() == other.sign())
            m_kind = PLUS_INFINITY;
        else
            m_kind = MINUS_INFINITY;
        m_value.reset();
        return *this;
    }

    SASSERT(m_kind == FINITE);
    m_value *= other.m_value;
    return *this;
}

void ext_numeral::expt(unsigned n) {
    switch (m_kind) {
    case MINUS_INFINITY:
        if (n % 2 == 0)
            m_kind = PLUS_INFINITY;
        return;
    case FINITE:
        m_value = m_value.expt(n);
        break;
    case PLUS_INFINITY:
        // do nothing
        break;
    }
}

void ext_numeral::inv() {
    SASSERT(!is_zero());
    if (is_infinite()) {
        m_kind = FINITE;
        m_value.reset();
    }
    else {
        m_value = rational(1) / m_value;
    }
}

void ext_numeral::display(std::ostream & out) const {
    switch (m_kind) {
    case MINUS_INFINITY:
        out << "-oo";
        break;
    case FINITE:
        out << m_value;
        break;
    case PLUS_INFINITY:
        out << "oo";
        break;
    }
}

bool operator==(ext_numeral const & n1, ext_numeral const & n2) {
    return n1.m_kind == n2.m_kind && (n1.is_infinite() || n1.m_value == n2.m_value);
}

bool operator<(ext_numeral const & n1, ext_numeral const & n2) {
    if (n1.is_infinite())
        return n1.m_kind == ext_numeral::MINUS_INFINITY && n2.m_kind != ext_numeral::MINUS_INFINITY;
    if (n2.is_infinite())
        return n2.m_kind != ext_numeral::MINUS_INFINITY;
    return n1.m_value < n2.m_value;
}

/**
   \brief Create interval (-oo, oo)
*/
interval::interval(v_dependency_manager & m):
    m_manager(m),
    m_lower(false),
    m_upper(true),
    m_lower_open(true),
    m_upper_open(true),
    m_lower_dep(0),
    m_upper_dep(0) {
}

/**
   \brief Create intervals [l,u], (l,u], [l, u), (l,u), where l and u are numerals.
*/
interval::interval(v_dependency_manager & m, rational const & lower, bool l_open, v_dependency * l_dep, rational const & upper, bool u_open, v_dependency * u_dep):
    m_manager(m),
    m_lower(lower),
    m_upper(upper),
    m_lower_open(l_open),
    m_upper_open(u_open),
    m_lower_dep(l_dep),
    m_upper_dep(u_dep) {
    SASSERT(lower <= upper);
    SASSERT(lower != upper || !l_open || !u_open);
}

/**
   \brief Create intervals [l,u], (l,u], [l, u), (l,u), where l and u are ext_numerals.
*/
interval::interval(v_dependency_manager & m, ext_numeral const & lower, bool l_open, v_dependency * l_dep, ext_numeral const & upper, bool u_open, v_dependency * u_dep):
    m_manager(m),
    m_lower(lower),
    m_upper(upper),
    m_lower_open(l_open),
    m_upper_open(u_open),
    m_lower_dep(l_dep),
    m_upper_dep(u_dep) {
    SASSERT(lower <= upper);
    SASSERT(lower != upper || !l_open || !u_open);
}

/**
   \brief Create interval [val,val]
*/
interval::interval(v_dependency_manager & m, rational const & val, v_dependency * l_dep, v_dependency * u_dep):
    m_manager(m),
    m_lower(val),
    m_upper(val),
    m_lower_open(false),
    m_upper_open(false),
    m_lower_dep(l_dep),
    m_upper_dep(u_dep) {
}
 
/**
   \brief Create intervals (-oo, val], (-oo, val), [val, oo), (val, oo)
*/
interval::interval(v_dependency_manager & m, rational const & val, bool open, bool lower, v_dependency * d):
    m_manager(m) {
    if (lower) {
        m_lower      = ext_numeral(val);
        m_lower_open = open;
        m_lower_dep  = d;
        m_upper      = ext_numeral(true);
        m_upper_open = true;
        m_upper_dep  = 0;
    }
    else {
        m_lower      = ext_numeral(false);
        m_lower_open = true;
        m_lower_dep  = 0;
        m_upper      = ext_numeral(val);
        m_upper_open = open;
        m_upper_dep  = d;
    }
}

interval::interval(interval const & other):
    m_manager(other.m_manager),
    m_lower(other.m_lower),
    m_upper(other.m_upper),
    m_lower_open(other.m_lower_open),
    m_upper_open(other.m_upper_open),
    m_lower_dep(other.m_lower_dep),
    m_upper_dep(other.m_upper_dep) {
}

interval & interval::operator=(interval const & other) {
    m_lower = other.m_lower;
    m_upper = other.m_upper;
    m_lower_open = other.m_lower_open;
    m_upper_open = other.m_upper_open;
    m_lower_dep  = other.m_lower_dep;
    m_upper_dep  = other.m_upper_dep;
    return *this;
}

interval & interval::operator+=(interval const & other) {
    m_lower      += other.m_lower;
    m_upper      += other.m_upper;
    m_lower_open |= other.m_lower_open;
    m_upper_open |= other.m_upper_open;
    m_lower_dep   = m_lower.is_infinite() ? 0 : m_manager.mk_join(m_lower_dep, other.m_lower_dep);
    m_upper_dep   = m_upper.is_infinite() ? 0 : m_manager.mk_join(m_upper_dep, other.m_upper_dep);
    return *this;
}

void interval::neg() {
    std::swap(m_lower, m_upper);
    std::swap(m_lower_open, m_upper_open);
    std::swap(m_lower_dep, m_upper_dep);
    m_lower.neg();
    m_upper.neg();
}

interval & interval::operator-=(interval const & other) {
    interval tmp(other);
    tmp.neg();
    return operator+=(tmp);
}

v_dependency * interval::join(v_dependency * d1, v_dependency * d2, v_dependency * d3, v_dependency * d4) { 
    return m_manager.mk_join(m_manager.mk_join(d1, d2), m_manager.mk_join(d3,d4)); 
}

/**
   \brief Create a new v_dependency using d1, d2, and (opt1 or opt2).
*/
v_dependency * interval::join_opt(v_dependency * d1, v_dependency * d2, v_dependency * opt1, v_dependency * opt2) {
    if (opt1 == d1 || opt1 == d2)
        return join(d1, d2);
    if (opt2 == d1 || opt2 == d2)
        return join(d1, d2);
    if (opt1 == 0 || opt2 == 0)
        return join(d1, d2);
    // TODO: more opts...
    return join(d1, d2, opt1);
}

interval & interval::operator*=(interval const & other) {
#if Z3DEBUG || _TRACE
    bool contains_zero1 = contains_zero();
    bool contains_zero2 = other.contains_zero();
#endif
    if (is_zero()) {
        return *this;
    }
    if (other.is_zero()) {
        *this = other;
        m_lower_dep = m_manager.mk_join(m_lower_dep, m_upper_dep);
        m_upper_dep = m_lower_dep;
        return *this;
    }

    ext_numeral const & a = m_lower;
    ext_numeral const & b = m_upper;
    ext_numeral const & c = other.m_lower;
    ext_numeral const & d = other.m_upper;
    bool a_o = m_lower_open;
    bool b_o = m_upper_open;
    bool c_o = other.m_lower_open;
    bool d_o = other.m_upper_open;
    v_dependency * a_d = m_lower_dep;
    v_dependency * b_d = m_upper_dep;
    v_dependency * c_d = other.m_lower_dep;
    v_dependency * d_d = other.m_upper_dep;

    TRACE("interval_bug", tout << "operator*= " << *this << " " << other << "\n";);
    
    if (is_N()) {
        if (other.is_N()) {
            // x <= b <= 0, y <= d <= 0 --> b*d <= x*y
            // a <= x <= b <= 0, c <= y <= d <= 0 --> x*y <= a*c  (we can use the fact that x or y is always negative (i.e., b is neg or d is neg))
            TRACE("interval_bug", tout << "(N, N)\n";);
            ext_numeral new_lower = b * d;
            ext_numeral new_upper = a * c;
            // if b = 0 (and the interval is closed), then the lower bound is closed
            m_lower_open = (is_N0() || other.is_N0()) ? false : (b_o || d_o);
            m_upper_open = a_o || c_o; SASSERT(a.is_neg() && c.is_neg());
            m_lower      = new_lower;
            m_upper      = new_upper;
            m_lower_dep  = m_lower.is_infinite() ? 0 : join(b_d, d_d);
            m_upper_dep  = m_upper.is_infinite() ? 0 : join_opt(a_d, c_d, b_d, d_d);
        }
        else if (other.is_M()) {
            // a <= x <= b <= 0,  y <= d, d > 0 --> a*d <= x*y (uses the fact that b is not positive)
            // a <= x <= b <= 0,  c <= y, c < 0 --> x*y <= a*c (uses the fact that b is not positive)
            TRACE("interval_bug", tout << "(N, M)\n";);
            ext_numeral new_lower = a * d; SASSERT(new_lower.is_neg());
            ext_numeral new_upper = a * c; SASSERT(new_upper.is_pos());
            m_lower_open = a_o || d_o;
            m_upper_open = a_o || c_o;
            m_lower      = new_lower;
            m_upper      = new_upper;
            m_lower_dep  = m_lower.is_infinite() ? 0 : join(a_d, d_d, b_d);
            m_upper_dep  = m_upper.is_infinite() ? 0 : join(a_d, c_d, b_d);
        }
        else {
            // a <= x <= b <= 0, 0 <= c <= y <= d --> a*d <= x*y (uses the fact that x is neg (b is not positive) or y is pos (c is not negative))
            // x <= b <= 0,  0 <= c <= y --> x*y <= b*c
            TRACE("interval_bug", tout << "(N, P)\n";);
            SASSERT(other.is_P());
            ext_numeral new_lower = a * d;
            ext_numeral new_upper = b * c;
            bool is_N0_old = is_N0(); // see comment in (P, N) case
            m_lower_open = a_o || d_o; SASSERT(a.is_neg() && d.is_pos());
            m_upper_open = (is_N0_old || other.is_P0()) ? false : (b_o || c_o);
            m_lower      = new_lower;
            m_upper      = new_upper;
            m_lower_dep  = m_lower.is_infinite() ? 0 : join_opt(a_d, d_d, b_d, c_d);
            m_upper_dep  = m_upper.is_infinite() ? 0 : join(b_d, c_d);
        }
    }
    else if (is_M()) {
        if (other.is_N()) {
            // b > 0, x <= b,  c <= y <= d <= 0 --> b*c <= x*y (uses the fact that d is not positive)
            // a < 0, a <= x,  c <= y <= d <= 0 --> x*y <= a*c (uses the fact that d is not positive)
            TRACE("interval_bug", tout << "(M, N)\n";);
            ext_numeral new_lower = b * c; SASSERT(new_lower.is_neg());
            ext_numeral new_upper = a * c; SASSERT(new_upper.is_pos());
            m_lower_open = b_o || c_o; SASSERT(b.is_pos() && c.is_neg());
            m_upper_open = a_o || c_o; SASSERT(a.is_neg() && c.is_neg());
            m_lower      = new_lower;
            m_upper      = new_upper;
            m_lower_dep  = m_lower.is_infinite() ? 0 : join(b_d, c_d, d_d);
            m_upper_dep  = m_upper.is_infinite() ? 0 : join(a_d, c_d, d_d);
        }
        else if (other.is_M()) {
            TRACE("interval_bug", tout << "(M, M)\n";);
            SASSERT(!a.is_zero() && !b.is_zero() && !c.is_zero() && !d.is_zero());
            ext_numeral ad = a*d; SASSERT(!ad.is_zero());
            ext_numeral bc = b*c; SASSERT(!bc.is_zero());
            ext_numeral ac = a*c; SASSERT(!ac.is_zero());
            ext_numeral bd = b*d; SASSERT(!bd.is_zero());
            bool        ad_o = a_o || d_o;
            bool        bc_o = b_o || c_o;
            bool        ac_o = a_o || c_o;
            bool        bd_o = b_o || d_o;
            if (ad < bc || (ad == bc && !ad_o && bc_o)) {
                m_lower       = ad;
                m_lower_open  = ad_o;
            }
            else {
                m_lower       = bc;
                m_lower_open  = bc_o;
            }
            if (ac > bd || (ac == bd && !ac_o && bd_o)) {
                m_upper       = ac;
                m_upper_open  = ac_o;
            }
            else {
                m_upper       = bd;
                m_upper_open  = bd_o;
            }
            m_lower_dep = m_lower.is_infinite() ? 0 : join(a_d, b_d, c_d, d_d);
            m_upper_dep = m_upper.is_infinite() ? 0 : join(a_d, b_d, c_d, d_d);
        }
        else {
            // a < 0, a <= x, 0 <= c <= y <= d --> a*d <= x*y (uses the fact that c is not negative)
            // b > 0, x <= b, 0 <= c <= y <= d --> x*y <= b*d (uses the fact that c is not negative)
            TRACE("interval_bug", tout << "(M, P)\n";);
            SASSERT(other.is_P());
            ext_numeral new_lower = a * d; SASSERT(new_lower.is_neg());
            ext_numeral new_upper = b * d; SASSERT(new_upper.is_pos());
            m_lower_open = a_o || d_o; SASSERT(a.is_neg() && d.is_pos());
            m_upper_open = b_o || d_o; SASSERT(b.is_pos() && d.is_pos());
            m_lower      = new_lower;
            m_upper      = new_upper;
            m_lower_dep  = m_lower.is_infinite() ? 0 : join(a_d, d_d, c_d);
            m_upper_dep  = m_upper.is_infinite() ? 0 : join(b_d, d_d, c_d);
        }
    }
    else {
        SASSERT(is_P());
        if (other.is_N()) {
            // 0 <= a <= x <= b,   c <= y <= d <= 0  -->  x*y <= b*c (uses the fact that x is pos (a is not neg) or y is neg (d is not pos))
            // 0 <= a <= x,  y <= d <= 0  --> a*d <= x*y
            TRACE("interval_bug", tout << "(P, N)\n";);
            ext_numeral new_lower = b * c;
            ext_numeral new_upper = a * d;
            bool is_P0_old = is_P0(); // cache the value of is_P0(), since it may be affected by the next update.
            m_lower_open = b_o || c_o; SASSERT(b.is_pos() && c.is_neg());
            m_upper_open = (is_P0_old || other.is_N0()) ? false : a_o || d_o;
            m_lower      = new_lower;
            m_upper      = new_upper;
            m_lower_dep  = m_lower.is_infinite() ? 0 : join_opt(b_d, c_d, a_d, d_d);
            m_upper_dep  = m_upper.is_infinite() ? 0 : join(a_d, d_d);
        }
        else if (other.is_M()) {
            // 0 <= a <= x <= b,  c <= y --> b*c <= x*y (uses the fact that a is not negative)
            // 0 <= a <= x <= b,  y <= d --> x*y <= b*d (uses the fact that a is not negative)
            TRACE("interval_bug", tout << "(P, M)\n";);
            ext_numeral new_lower = b * c; SASSERT(new_lower.is_neg());
            ext_numeral new_upper = b * d; SASSERT(new_upper.is_pos());
            m_lower_open = b_o || c_o;
            m_upper_open = b_o || d_o;
            m_lower      = new_lower;
            m_upper      = new_upper;
            m_lower_dep  = m_lower.is_infinite() ? 0 : join(b_d, c_d, a_d);
            m_upper_dep  = m_upper.is_infinite() ? 0 : join(b_d, d_d, a_d);
        }
        else {
            // 0 <= a <= x, 0 <= c <= y --> a*c <= x*y 
            // x <= b, y <= d --> x*y <= b*d (uses the fact that x is pos (a is not negative) or y is pos (c is not negative))
            TRACE("interval_bug", tout << "(P, P)\n";);
            SASSERT(other.is_P());
            ext_numeral new_lower = a * c;
            ext_numeral new_upper = b * d;
            m_lower_open = (is_P0() || other.is_P0()) ? false : a_o || c_o;
            m_upper_open = b_o || d_o; SASSERT(b.is_pos() && d.is_pos());
            m_lower      = new_lower;
            m_upper      = new_upper;
            m_lower_dep  = m_lower.is_infinite() ? 0 : join(a_d, c_d);
            m_upper_dep  = m_upper.is_infinite() ? 0 : join_opt(b_d, d_d, a_d, c_d);
        }
    }
    TRACE("interval_bug", tout << "operator*= result: " << *this << "\n";);
    CTRACE("interval", !(!(contains_zero1 || contains_zero2) || contains_zero()), 
           tout << "contains_zero1: " << contains_zero1 << ", contains_zero2: " << contains_zero2 << ", contains_zero(): " << contains_zero() << "\n";);
    SASSERT(!(contains_zero1 || contains_zero2) || contains_zero());
    return *this;
}

bool interval::contains_zero() const {
    TRACE("interval_zero_bug", tout << "contains_zero info: " << *this << "\n";
          tout << "m_lower.is_neg(): " << m_lower.is_neg() << "\n";
          tout << "m_lower.is_zero:  " << m_lower.is_zero() << "\n";
          tout << "m_lower_open:     " << m_lower_open << "\n";
          tout << "m_upper.is_pos(): " << m_upper.is_pos() << "\n";
          tout << "m_upper.is_zero:  " << m_upper.is_zero() << "\n";
          tout << "m_upper_open:     " << m_upper_open << "\n";
          tout << "result:           " << ((m_lower.is_neg() || (m_lower.is_zero() && !m_lower_open)) && (m_upper.is_pos() || (m_upper.is_zero() && !m_upper_open))) << "\n";);
    return 
        (m_lower.is_neg() || (m_lower.is_zero() && !m_lower_open)) &&
        (m_upper.is_pos() || (m_upper.is_zero() && !m_upper_open));
}

bool interval::contains(rational const& v) const {
    if (!inf().is_infinite()) {
        if (v < inf().to_rational()) return false;
        if (v == inf().to_rational() && m_lower_open) return false;
    }
    if (!sup().is_infinite()) {
        if (v > sup().to_rational()) return false;
        if (v == sup().to_rational() && m_upper_open) return false;
    }
    return true;
}

interval & interval::inv() {
    // If the interval [l,u] does not contain 0, then 1/[l,u] = [1/u, 1/l]
    SASSERT(!contains_zero());
    if (is_P1()) {
        // 0 < a <= x --> 1/x <= 1/a
        // 0 < a <= x <= b --> 1/b <= 1/x (use lower and upper bounds)
        ext_numeral new_lower = m_upper; SASSERT(!m_upper.is_zero());
        new_lower.inv();
        ext_numeral new_upper;
        if (m_lower.is_zero()) {
            SASSERT(m_lower_open);
            ext_numeral plus_infinity(true); 
            new_upper = plus_infinity;
        }
        else {
            new_upper = m_lower;
            new_upper.inv();
        }
        m_lower = new_lower;
        m_upper = new_upper;
        std::swap(m_lower_open, m_upper_open);
        v_dependency * new_upper_dep = m_lower_dep;
        SASSERT(!m_lower.is_infinite());
        m_lower_dep = m_manager.mk_join(m_lower_dep, m_upper_dep);
        m_upper_dep = new_upper_dep;
    }
    else if (is_N1()) {
        // x <= a < 0 --> 1/a <= 1/x
        // b <= x <= a < 0 --> 1/b <= 1/x (use lower and upper bounds)
        ext_numeral new_upper = m_lower; SASSERT(!m_lower.is_zero());
        new_upper.inv();
        ext_numeral new_lower;
        if (m_upper.is_zero()) {
            SASSERT(m_upper_open);
            ext_numeral minus_infinity(false);
            new_lower = minus_infinity;
        }
        else {
            new_lower = m_upper;
            new_lower.inv();
        }
        m_lower = new_lower;
        m_upper = new_upper;
        std::swap(m_lower_open, m_upper_open);
        v_dependency * new_lower_dep = m_upper_dep;
        SASSERT(!m_upper.is_infinite());
        m_upper_dep = m_manager.mk_join(m_lower_dep, m_upper_dep);
        m_lower_dep = new_lower_dep;
    }
    else {
        UNREACHABLE();
    }
    return *this;
}

interval & interval::operator/=(interval const & other) {
    SASSERT(!other.contains_zero());
    if (is_zero()) {
        // 0/other = 0 if other != 0
        TRACE("interval", other.display_with_dependencies(tout););
        if (other.m_lower.is_pos() || (other.m_lower.is_zero() && other.m_lower_open)) {
            // other.lower > 0
            m_lower_dep  = join(m_lower_dep, other.m_lower_dep);
            m_upper_dep  = join(m_upper_dep, other.m_lower_dep);
        }
        else {
            // assertion must hold since !other.contains_zero()
            SASSERT(other.m_upper.is_neg() || (other.m_upper.is_zero() && other.m_upper_open));
            // other.upper < 0
            m_lower_dep  = join(m_lower_dep, other.m_upper_dep);
            m_upper_dep  = join(m_upper_dep, other.m_upper_dep);
        }
        return *this;
    }
    else {
        interval tmp(other);
        tmp.inv();
        return operator*=(tmp);
    }
}

void interval::expt(unsigned n) {
    if (n == 1)
        return;
    if (n % 2 == 0) {
        if (m_lower.is_pos()) {
            // [l, u]^n = [l^n, u^n] if l > 0
            // 0 < a <= x      --> a^n <= x^n (lower bound guarantees that is positive)
            // 0 < a <= x <= b --> x^n <= b^n (use lower and upper bound -- need the fact that x is positive)
            m_lower.expt(n);
            m_upper.expt(n);
            m_upper_dep = m_upper.is_infinite() ? 0 : m_manager.mk_join(m_lower_dep, m_upper_dep);
        }
        else if (m_upper.is_neg()) {
            // [l, u]^n = [u^n, l^n] if u < 0
            // a <= x <= b < 0   -->  x^n <= a^n (use lower and upper bound -- need the fact that x is negative)
            // x <= b < 0        -->  b^n <= x^n 
            std::swap(m_lower, m_upper);
            std::swap(m_lower_open, m_upper_open);
            std::swap(m_lower_dep, m_upper_dep);
            m_lower.expt(n);
            m_upper.expt(n);
            m_upper_dep = m_upper.is_infinite() ? 0 : m_manager.mk_join(m_lower_dep, m_upper_dep);
        }
        else {
            // [l, u]^n = [0, max{l^n, u^n}] otherwise
            // we need both bounds to justify upper bound
            TRACE("interval", tout << "before: " << m_lower << " " << m_upper << " " << n << "\n";);
            m_lower.expt(n);
            m_upper.expt(n);
            TRACE("interval", tout << "after: " << m_lower << " " << m_upper << "\n";);
            if (m_lower > m_upper || (m_lower == m_upper && !m_lower_open && m_upper_open)) {
                m_upper      = m_lower;
                m_upper_open = m_lower_open;
            }
            m_upper_dep  = m_upper.is_infinite() ? 0 : m_manager.mk_join(m_lower_dep, m_upper_dep); 
            m_lower      = ext_numeral(0);
            m_lower_open = false;
            m_lower_dep  = 0;
        }
    }
    else {
        // Remark: when n is odd x^n is monotonic.
        m_lower.expt(n);
        m_upper.expt(n);
    }
}

void interval::display(std::ostream & out) const {
    out << (m_lower_open ? "(" : "[") << m_lower << ", " << m_upper << (m_upper_open ? ")" : "]");
}

void interval::display_with_dependencies(std::ostream & out) const {
    ptr_vector<void> vs;
    m_manager.linearize(m_lower_dep, vs);
    m_manager.linearize(m_upper_dep, vs);
    out << "[";
    display(out);
    out << ", ";
    bool first = true;
    ::display(out, vs.begin(), vs.end(), ", ", first);
    out << "]";
}




