/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    old_interval.h

Abstract:

    Old interval class. It is still used in some modules.

Author:

    Leonardo de Moura (leonardo) 2008-12-09.

Revision History:

--*/
#ifndef OLD_INTERVAL_H_
#define OLD_INTERVAL_H_

#include"rational.h"
#include"dependency.h"

class ext_numeral {
public:
    enum kind { MINUS_INFINITY, FINITE, PLUS_INFINITY };
private:
    kind     m_kind;
    rational m_value; 
    explicit ext_numeral(kind k):m_kind(k) {}
public:
    ext_numeral():m_kind(FINITE) {} /* zero */
    explicit ext_numeral(bool plus_infinity):m_kind(plus_infinity ? PLUS_INFINITY : MINUS_INFINITY) {}
    explicit ext_numeral(rational const & val):m_kind(FINITE), m_value(val) {}
    explicit ext_numeral(int i):m_kind(FINITE), m_value(i) {}
    ext_numeral(ext_numeral const & other):m_kind(other.m_kind), m_value(other.m_value) {}
    bool is_infinite() const { return m_kind != FINITE; }
    bool sign() const { return m_kind == MINUS_INFINITY || (m_kind == FINITE && m_value.is_neg()); }
    void neg();
    bool is_zero() const { return m_kind == FINITE && m_value.is_zero(); }
    bool is_neg() const { return sign(); }
    bool is_pos() const { return !is_neg() && !is_zero(); }
    rational const & to_rational() const { SASSERT(!is_infinite()); return m_value; }
    ext_numeral & operator+=(ext_numeral const & other);
    ext_numeral & operator-=(ext_numeral const & other);
    ext_numeral & operator*=(ext_numeral const & other);
    void inv();
    void expt(unsigned n);
    void display(std::ostream & out) const;
    friend bool operator==(ext_numeral const & n1, ext_numeral const & n2);
    friend bool operator<(ext_numeral const & n1, ext_numeral const & n2);
};

bool operator==(ext_numeral const & n1, ext_numeral const & n2);
bool operator<(ext_numeral const & n1, ext_numeral const & n2);
inline bool operator!=(ext_numeral const & n1, ext_numeral const & n2) { return !operator==(n1,n2); }
inline bool operator>(ext_numeral const & n1, ext_numeral const & n2) { return operator<(n2, n1); }
inline bool operator<=(ext_numeral const & n1, ext_numeral const & n2) { return !operator>(n1, n2); }
inline bool operator>=(ext_numeral const & n1, ext_numeral const & n2) { return !operator<(n1, n2); }
inline ext_numeral operator+(ext_numeral const & n1, ext_numeral const & n2) { return ext_numeral(n1) += n2; }
inline ext_numeral operator-(ext_numeral const & n1, ext_numeral const & n2) { return ext_numeral(n1) -= n2; }
inline ext_numeral operator*(ext_numeral const & n1, ext_numeral const & n2) { return ext_numeral(n1) *= n2; }
inline std::ostream & operator<<(std::ostream & out, ext_numeral const & n) { n.display(out); return out; }

class old_interval {
    v_dependency_manager & m_manager;
    ext_numeral            m_lower;
    ext_numeral            m_upper;
    bool                   m_lower_open;
    bool                   m_upper_open;
    v_dependency *         m_lower_dep; // justification for the lower bound
    v_dependency *         m_upper_dep; // justification for the upper bound
    
    v_dependency * join(v_dependency * d1, v_dependency * d2) { return m_manager.mk_join(d1, d2); }
    v_dependency * join(v_dependency * d1, v_dependency * d2, v_dependency * d3) { return m_manager.mk_join(m_manager.mk_join(d1, d2), d3); }
    v_dependency * join(v_dependency * d1, v_dependency * d2, v_dependency * d3, v_dependency * d4);
    v_dependency * join_opt(v_dependency * d1, v_dependency * d2, v_dependency * opt1, v_dependency * opt2);

public:
    explicit old_interval(v_dependency_manager & m);  
    explicit old_interval(v_dependency_manager & m, rational const & lower, bool l_open, v_dependency * l_dep, rational const & upper, bool u_open, v_dependency * u_dep);
    explicit old_interval(v_dependency_manager & m, rational const & val, v_dependency * l_dep = 0, v_dependency * u_dep = 0);
    explicit old_interval(v_dependency_manager & m, rational const & val, bool open, bool lower, v_dependency * d);
    explicit old_interval(v_dependency_manager & m, ext_numeral const& lower, bool l_open, v_dependency * l_dep, ext_numeral const & upper, bool u_open, v_dependency * u_dep);
    old_interval(old_interval const & other);
    
    bool minus_infinity() const { return m_lower.is_infinite(); }
    bool plus_infinity() const { return m_upper.is_infinite(); }
    bool is_lower_open() const { return m_lower_open; }
    bool is_upper_open() const { return m_upper_open; }
    v_dependency * get_lower_dependencies() const { return m_lower_dep; }
    v_dependency * get_upper_dependencies() const { return m_upper_dep; }
    rational const & get_lower_value() const { SASSERT(!minus_infinity()); return m_lower.to_rational(); }
    rational const & get_upper_value() const { SASSERT(!plus_infinity()); return m_upper.to_rational(); }
    old_interval & operator=(old_interval const & other);
    old_interval & operator+=(old_interval const & other);
    old_interval & operator-=(old_interval const & other);
    old_interval & operator*=(old_interval const & other);
    old_interval & operator*=(rational const & value);
    old_interval & operator/=(old_interval const & other);
    bool operator==(old_interval const & other) const { return m_lower == other.m_lower && m_upper == other.m_upper && m_lower_open == other.m_lower_open && m_upper_open == other.m_upper_open; }
    bool contains_zero() const;
    bool contains(rational const& v) const;
    old_interval & inv();
    void expt(unsigned n);
    void neg();
    void display(std::ostream & out) const;
    void display_with_dependencies(std::ostream & out) const;
    bool is_P() const { return m_lower.is_pos() || m_lower.is_zero(); }
    bool is_P0() const { return m_lower.is_zero() && !m_lower_open; }
    bool is_P1() const { return m_lower.is_pos() || (m_lower.is_zero() && m_lower_open); }
    bool is_N() const { return m_upper.is_neg() || m_upper.is_zero(); }
    bool is_N0() const { return m_upper.is_zero() && !m_upper_open; }
    bool is_N1() const { return m_upper.is_neg() || (m_upper.is_zero() && m_upper_open); }
    bool is_M() const { return m_lower.is_neg() && m_upper.is_pos(); }
    bool is_zero() const { return m_lower.is_zero() && m_upper.is_zero(); }

    ext_numeral const& inf() const { return m_lower; }
    ext_numeral const& sup() const { return m_upper; }
};

inline old_interval operator+(old_interval const & i1, old_interval const & i2) { return old_interval(i1) += i2; }
inline old_interval operator-(old_interval const & i1, old_interval const & i2) { return old_interval(i1) -= i2; }
inline old_interval operator*(old_interval const & i1, old_interval const & i2) { return old_interval(i1) *= i2; }
inline old_interval operator/(old_interval const & i1, old_interval const & i2) { return old_interval(i1) /= i2; }
inline old_interval expt(old_interval const & i, unsigned n) { old_interval tmp(i); tmp.expt(n); return tmp; }
inline std::ostream & operator<<(std::ostream & out, old_interval const & i) { i.display(out); return out; }

struct interval_detail{};
inline std::pair<old_interval, interval_detail> wd(old_interval const & i) { interval_detail d; return std::make_pair(i, d); }
inline std::ostream & operator<<(std::ostream & out, std::pair<old_interval, interval_detail> const & p) { p.first.display_with_dependencies(out); return out; }

// allow "customers" of this file to keep using interval
#define interval old_interval

#endif /* OLD_INTERVAL_H_ */

