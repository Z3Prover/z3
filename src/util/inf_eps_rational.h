/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    inf_eps_rational.h

Abstract:

    Rational numbers with infinity and epsilon.

Author:

    Nikolaj Bjorner (nbjorner) 2013-4-23.

Revision History:

--*/
#pragma once
#include<stdlib.h>
#include<string>
#include "util/debug.h"
#include "util/vector.h"
#include "util/rational.h"
#include "util/inf_rational.h"

template<typename Numeral>
class inf_eps_rational {
    rational    m_infty;
    Numeral     m_r;
 public:

    unsigned hash() const { 
        return m_infty.hash() ^ m_r.hash();
    }

    struct hash_proc {  unsigned operator()(inf_eps_rational const& r) const { return r.hash(); }  };

    struct eq_proc { bool operator()(inf_eps_rational const& r1, inf_eps_rational const& r2) const { return r1 == r2; } };

    void swap(inf_eps_rational & n) { 
        m_infty.swap(n.m_infty);
        m_r.swap(n.m_r);
    }

    std::string to_string() const {
        if (m_infty.is_zero()) {
            return m_r.to_string();
        }
        std::string si;
        if (m_infty.is_one()) {
            si = "oo";
        }
        else if (m_infty.is_minus_one()) {
            si = "-oo";
        }
        else {
            si = m_infty.to_string() += "*oo";
        }
        if (m_r.is_zero()) {
            return si;
        }
        std::string s = "(";
        s += si;
        s += " + ";
        s += m_r.to_string();
        s += ")";
        return s;
    }

    inf_eps_rational() = default;

    explicit inf_eps_rational(int n):
        m_infty(),
        m_r(n)
    {}

    explicit inf_eps_rational(Numeral const& r):
        m_infty(),
        m_r(r)
    {}

    explicit inf_eps_rational(rational const& i, Numeral const& r):
        m_infty(i),
        m_r(r) {
    }

    /**
       \brief Set inf_eps_rational to 0.
    */
    void reset() {
        m_infty.reset();
        m_r.reset();
    }

    bool is_int() const { 
        return m_infty.is_zero() && m_r.is_int();
    }

    bool is_int64() const { 
        return m_infty.is_zero() && m_r.is_int64();
    }

    bool is_uint64() const { 
        return m_infty.is_zero() && m_r.is_uint64();
    }

    bool is_rational() const { return m_infty.is_zero() && m_r.is_rational(); }

    int64_t get_int64() const {
        SASSERT(is_int64());
        return m_r.get_int64();
    }

    uint64_t get_uint64() const {
        SASSERT(is_uint64());
        return m_r.get_uint64();
    }

    Numeral const& get_numeral() const {
        return m_r;
    }

    rational const& get_rational() const {
        return m_r.get_rational();
    }

    rational const& get_infinitesimal() const {
        return m_r.get_infinitesimal();
    }

    rational const& get_infinity() const {
        return m_infty;
    }

    bool is_finite() const {
        return m_infty.is_zero();
    }

    static inf_eps_rational zero() {
        return inf_eps_rational(Numeral::zero());
    }

    static inf_eps_rational one() {
        return inf_eps_rational(Numeral::one());
    }

    static inf_eps_rational minus_one() {
        return inf_eps_rational(Numeral::minus_one());
    }

    static inf_eps_rational infinity() {
        return inf_eps_rational(rational::one(), Numeral::zero());
    }

    inf_eps_rational & operator=(const Numeral & r) {
        m_infty.reset();
        m_r = r;
        return *this;
    }

    inf_eps_rational & operator+=(const inf_eps_rational & r) { 
        m_infty  += r.m_infty;
        m_r      += r.m_r;
        return *this; 
    }

    inf_eps_rational & operator-=(const inf_eps_rational & r) { 
        m_infty  -= r.m_infty;
        m_r      -= r.m_r;
        return *this; 
    }

    inf_eps_rational & operator-=(const inf_rational & r) { 
        m_r      -= r;
        return *this; 
    }

    inf_eps_rational & operator+=(const inf_rational & r) { 
        m_r      += r;
        return *this; 
    }

    inf_eps_rational & operator+=(const rational & r) { 
        m_r  += r;
        return *this; 
    }

    inf_eps_rational & operator-=(const rational & r) { 
        m_r  -= r;
        return *this; 
    }

    inf_eps_rational & operator*=(const rational & r1) {
        m_infty  *= r1;
        m_r *= r1;
        return *this;
    }

    inf_eps_rational & operator/=(const rational & r) {
        m_infty /= r;
        m_r /= r;
        return *this;
    }


    inf_eps_rational & operator++() {
        ++m_r;
        return *this;
    }

    const inf_eps_rational operator++(int) { inf_eps_rational tmp(*this); ++(*this); return tmp; }
  
    inf_eps_rational & operator--() {
        --m_r;
        return *this;
    }

    const inf_eps_rational operator--(int) { inf_eps_rational tmp(*this); --(*this); return tmp; }

    friend inline bool operator==(const inf_eps_rational & r1, const inf_eps_rational & r2) {
        return r1.m_infty == r2.m_infty && r1.m_r == r2.m_r;
    }

    friend inline bool operator==(const rational & r1, const inf_eps_rational & r2) {
        return r1 == r2.m_infty && r2.m_r.is_zero();
    }

    friend inline bool operator==(const inf_eps_rational & r1, const rational & r2) {
        return r1.m_infty == r2 && r1.m_r.is_zero();
    }

    friend inline bool operator<(const inf_eps_rational & r1, const inf_eps_rational & r2) { 
        return 
            (r1.m_infty < r2.m_infty) ||
            (r1.m_infty == r2.m_infty && r1.m_r < r2.m_r);
    }

    friend inline bool operator<(const rational & r1, const inf_eps_rational & r2) { 
        return 
            r2.m_infty.is_pos() ||
            (r2.m_infty.is_zero() && r1 < r2.m_r);
    }

    friend inline bool operator<(const inf_eps_rational & r1, const rational & r2) { 
        return 
            r1.m_infty.is_neg() ||
            (r1.m_infty.is_zero() && r1.m_r < r2);
    }

    void neg() {
        m_infty.neg();
        m_r.neg();
    }

    bool is_zero() const {
        return m_infty.is_zero() && m_r.is_zero();
    }

    bool is_one() const {
        return m_infty.is_zero() && m_r.is_one();
    }

    bool is_minus_one() const {
        return m_infty.is_zero() && m_r.is_minus_one();
    }

    bool is_neg() const {
        return 
            m_infty.is_neg() || 
            (m_infty.is_zero() && m_r.is_neg());
    }
    
    bool is_pos() const {
        return 
            m_infty.is_pos() || 
            (m_infty.is_zero() && m_r.is_pos());
    }

    bool is_nonneg() const {
        return 
            m_infty.is_pos() ||
            (m_infty.is_zero() && m_r.is_nonneg());
    }

    bool is_nonpos() const {
        return 
            m_infty.is_neg() ||
            (m_infty.is_zero() && m_r.is_nonpos());
    }

    friend inline rational floor(const inf_eps_rational & r) {
        // SASSERT(r.m_infty.is_zero());
        return floor(r.m_r);
    }

    friend inline rational ceil(const inf_eps_rational & r) {
        // SASSERT(r.m_infty.is_zero());
        return ceil(r.m_r);
    }


    // Perform: this += c * k
    void addmul(const rational & c, const inf_eps_rational & k) {
        m_infty.addmul(c, k.m_infty);
        m_r.addmul(c, k.m_r);
    }

    // Perform: this += c * k
    void submul(const rational & c, const inf_eps_rational & k) {
        m_infty.submul(c, k.m_infty);
        m_r.submul(c, k.m_r);
    }
};

template<typename N>
inline bool operator!=(const inf_eps_rational<N> & r1, const inf_eps_rational<N> & r2) { 
    return !operator==(r1, r2); 
}

template<typename N>
inline bool operator!=(const rational & r1, const inf_eps_rational<N> & r2) { 
    return !operator==(r1, r2); 
}

template<typename N>
inline bool operator!=(const inf_eps_rational<N> & r1, const rational & r2) { 
    return !operator==(r1, r2); 
}

template<typename N>
inline bool operator>(const inf_eps_rational<N> & r1, const inf_eps_rational<N> & r2) { 
    return operator<(r2, r1); 
}

template<typename N>
inline bool operator>(const inf_eps_rational<N> & r1, const rational & r2) { 
    return operator<(r2, r1); 
}

template<typename N>
inline bool operator>(const rational & r1, const inf_eps_rational<N> & r2) { 
    return operator<(r2, r1); 
}

template<typename N>
inline bool operator<=(const inf_eps_rational<N> & r1, const inf_eps_rational<N> & r2) { 
    return !operator>(r1, r2); 
}

template<typename N>
inline bool operator<=(const rational & r1, const inf_eps_rational<N> & r2) { 
    return !operator>(r1, r2); 
}

template<typename N>
inline bool operator<=(const inf_eps_rational<N> & r1, const rational & r2) { 
    return !operator>(r1, r2); 
}

template<typename N>
inline bool operator>=(const inf_eps_rational<N> & r1, const inf_eps_rational<N> & r2) { 
    return !operator<(r1, r2); 
}

template<typename N>
inline bool operator>=(const rational & r1, const inf_eps_rational<N> & r2) { 
    return !operator<(r1, r2); 
}

template<typename N>
inline bool operator>=(const inf_eps_rational<N> & r1, const rational & r2) { 
    return !operator<(r1, r2); 
}

template<typename N>
inline inf_eps_rational<N> operator+(const inf_eps_rational<N> & r1, const inf_eps_rational<N> & r2) { 
    return inf_eps_rational<N>(r1) += r2; 
}

template<typename N>
inline inf_eps_rational<N> operator-(const inf_eps_rational<N> & r1, const inf_eps_rational<N> & r2) { 
    return inf_eps_rational<N>(r1) -= r2; 
}

template<typename N>
inline inf_eps_rational<N> operator-(const inf_eps_rational<N> & r) { 
    inf_eps_rational<N> result(r); 
    result.neg(); 
    return result; 
}

template<typename N>
inline inf_eps_rational<N> operator*(const rational & r1, const inf_eps_rational<N> & r2) {
    inf_eps_rational<N> result(r2);
    result *= r1;
    return result;
}

template<typename N>
inline inf_eps_rational<N> operator*(const inf_eps_rational<N> & r1, const rational & r2) {
    return r2 * r1;
}

template<typename N>
inline inf_eps_rational<N> operator/(const inf_eps_rational<N> & r1, const rational & r2) {
    inf_eps_rational<N> result(r1);
    result /= r2;
    return result;
}

template<typename N>
inline std::ostream & operator<<(std::ostream & target, const inf_eps_rational<N> & r) {
    target << r.to_string();
    return target;
}

template<typename N>
inline inf_eps_rational<N> abs(const inf_eps_rational<N> & r) {
    inf_eps_rational<N> result(r);
    if (result.is_neg()) {
        result.neg();
    }
    return result;
}

