/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    inf_rational.h

Abstract:

    Rational numbers with infenitesimals

Author:

    Leonardo de Moura (leonardo) 2006-09-18.
    Nikolaj Bjorner (nbjorner) 2006-10-24.

Revision History:

--*/
#ifndef INF_RATIONAL_H_
#define INF_RATIONAL_H_
#include<stdlib.h>
#include<string>
#include"debug.h"
#include"vector.h"
#include"rational.h"


class inf_rational {
    static inf_rational m_zero;
    static inf_rational m_one;
    static inf_rational m_minus_one;
    rational m_first;
    rational m_second;
 public:
    static void init(); // called from rational::initialize() only
    static void finalize();  // called from rational::finalize() only

    unsigned hash() const { 
        return m_first.hash() ^ (m_second.hash()+1);
    }

    struct hash_proc {  unsigned operator()(inf_rational const& r) const { return r.hash(); }  };

    struct eq_proc { bool operator()(inf_rational const& r1, inf_rational const& r2) const { return r1 == r2; } };

    void swap(inf_rational & n) { 
        m_first.swap(n.m_first);
        m_second.swap(n.m_second);
    }
    std::string to_string() const {
        if (m_second.is_zero()) {
            return m_first.to_string();
        }
        std::string s = "(";
        s += m_first.to_string();
        if (m_second.is_neg()) {
            s += " -e*";
        }
        else {
            s += " +e*";
        }
        s += abs(m_second).to_string();
        s += ")";
        return s;
    }

    inf_rational() {}

    inf_rational(const inf_rational & r): 
        m_first(r.m_first),
        m_second(r.m_second)
     {}

    explicit inf_rational(int n):
        m_first(rational(n)),
        m_second(rational())
    {}

    explicit inf_rational(int n, int d):
        m_first(rational(n,d)),
        m_second(rational())
    {}

    explicit inf_rational(rational const& r, bool pos_inf):
        m_first(r),
        m_second(pos_inf ? rational::one() : rational::minus_one())
    {}

    inf_rational(rational const& r):
        m_first(r)
    {
        m_second.reset();
    }

    inf_rational(rational const& r, rational const& i):
        m_first(r),
        m_second(i) {
    }

    ~inf_rational() {}

    /**
       \brief Set inf_rational to 0.
    */
    void reset() {
        m_first.reset();
        m_second.reset();
    }

    bool is_int() const { 
        return m_first.is_int() && m_second.is_zero();
    }

    bool is_int64() const { 
        return m_first.is_int64() && m_second.is_zero();
    }

    bool is_uint64() const { 
        return m_first.is_uint64() && m_second.is_zero();
    }

    bool is_rational() const { return m_second.is_zero(); }

    int64 get_int64() const {
	SASSERT(is_int64());
        return m_first.get_int64();
    }

    uint64 get_uint64() const {
	SASSERT(is_uint64());
        return m_first.get_uint64();
    }

    rational const& get_rational() const {
        return m_first;
    }

    rational const& get_infinitesimal() const {
        return m_second;
    }

    rational const & get_first() const { return m_first; }

    inf_rational & operator=(const inf_rational & r) {
        m_first = r.m_first;
        m_second = r.m_second;
	return *this;
    }

    inf_rational & operator=(const rational & r) {
        m_first = r;
        m_second.reset();
        return *this;
    }

    friend inline inf_rational numerator(const inf_rational & r) {
        SASSERT(r.m_second.is_zero());
        return inf_rational(numerator(r.m_first));
    }

    friend inline inf_rational denominator(const inf_rational & r) {
        SASSERT(r.m_second.is_zero());
        return inf_rational(denominator(r.m_first));
    }

    inf_rational & operator+=(const inf_rational & r) { 
        m_first  += r.m_first;
        m_second += r.m_second;
	return *this; 
    }

    inf_rational & operator-=(const inf_rational & r) { 
        m_first  -= r.m_first;
        m_second -= r.m_second;
	return *this; 
    }

    inf_rational & operator+=(const rational & r) { 
        m_first  += r;
	return *this; 
    }

    inf_rational & operator-=(const rational & r) { 
        m_first  -= r;
	return *this; 
    }

    inf_rational & operator*=(const rational & r1) {
        m_first  *= r1;
        m_second *= r1;
        return *this;
    }

    //
    // These operations get us out of the realm of inf_rational:
    // (r1 + e*k1)*(r2 + e*k2) = (r1*r2 + (r1*k2 + r2*k1)*e)
    //
    // inf_rational & operator*=(const inf_rational & r)
    // inf_rational & operator/=(const inf_rational & r)
    // inf_rational & operator%=(const inf_rational & r)
    // friend inline inf_rational div(const inf_rational & r1, const inf_rational & r2)
    // inf_rational expt(int n)
    // instead, we define operators that approximate some of these operations from above and below.
    
    friend inf_rational inf_mult(inf_rational const& r1, inf_rational const& r2);
    friend inf_rational sup_mult(inf_rational const& r1, inf_rational const& r2);

    friend inf_rational inf_div(inf_rational const& r1, inf_rational const& r2);
    friend inf_rational sup_div(inf_rational const& r1, inf_rational const& r2);

    friend inf_rational inf_power(inf_rational const& r1, unsigned n);
    friend inf_rational sup_power(inf_rational const& r1, unsigned n);

    friend inf_rational inf_root(inf_rational const& r1, unsigned n);
    friend inf_rational sup_root(inf_rational const& r1, unsigned n);

    inf_rational & operator/=(const rational & r) {
        m_first /= r;
        m_second /= r;
        return *this;
    }

    friend inline inf_rational operator*(const rational & r1, const inf_rational & r2);
    friend inline inf_rational operator*(const inf_rational & r1, const rational & r2);
    friend inline inf_rational operator/(const inf_rational & r1, const rational & r2);

    inf_rational & operator++() {
        ++m_first;
        return *this;
    }

    const inf_rational operator++(int) { inf_rational tmp(*this); ++(*this); return tmp; }
  
    inf_rational & operator--() {
        --m_first;
        return *this;
    }

    const inf_rational operator--(int) { inf_rational tmp(*this); --(*this); return tmp; }

    friend inline bool operator==(const inf_rational & r1, const inf_rational & r2) {
        return r1.m_first == r2.m_first && r1.m_second == r2.m_second;
    }

    friend inline bool operator==(const rational & r1, const inf_rational & r2) {
        return r1 == r2.m_first && r2.m_second.is_zero();
    }

    friend inline bool operator==(const inf_rational & r1, const rational & r2) {
        return r1.m_first == r2 && r1.m_second.is_zero();
    }

    friend inline bool operator<(const inf_rational & r1, const inf_rational & r2) { 
        return 
            (r1.m_first < r2.m_first) ||
            (r1.m_first == r2.m_first && r1.m_second < r2.m_second);
    }

    friend inline bool operator<(const rational & r1, const inf_rational & r2) { 
        return 
            (r1 < r2.m_first) ||
            (r1 == r2.m_first && r2.m_second.is_pos());
    }

    friend inline bool operator<(const inf_rational & r1, const rational & r2) { 
        return 
            (r1.m_first < r2) ||
            (r1.m_first == r2 && r1.m_second.is_neg());
    }

    void neg() {
        m_first.neg();
        m_second.neg();
    }

    bool is_zero() const {
        return m_first.is_zero() && m_second.is_zero();
    }

    bool is_one() const {
        return m_first.is_one() && m_second.is_zero();
    }

    bool is_minus_one() const {
        return m_first.is_minus_one() && m_second.is_zero();
    }

    bool is_neg() const {
        return 
            m_first.is_neg() || 
            (m_first.is_zero() && m_second.is_neg());
    }
    
    bool is_pos() const {
        return 
            m_first.is_pos() || 
            (m_first.is_zero() && m_second.is_pos());
    }

    bool is_nonneg() const {
        return 
            m_first.is_pos() ||
            (m_first.is_zero() && m_second.is_nonneg());
    }

    bool is_nonpos() const {
        return 
            m_first.is_neg() ||
            (m_first.is_zero() && m_second.is_nonpos());
    }

    friend inline rational floor(const inf_rational & r) {
        if (r.m_first.is_int()) {
            if (r.m_second.is_nonneg()) {
                return r.m_first;
            }
            return r.m_first - rational::one();
        }
        
        return floor(r.m_first);
    }

    friend inline rational ceil(const inf_rational & r) {
        if (r.m_first.is_int()) {
            if (r.m_second.is_nonpos()) {
                return r.m_first;
            }
            return r.m_first + rational::one();
        }
        
        return ceil(r.m_first);
    }

    static const inf_rational & zero() {
        return m_zero;
    }

    static const inf_rational & one() {
        return m_one;
    }

    static const inf_rational & minus_one() {
        return m_minus_one;
    }

    // Perform: this += c * k
    void addmul(const rational & c, const inf_rational & k) {
        m_first.addmul(c, k.m_first);
        m_second.addmul(c, k.m_second);
    }

    // Perform: this += c * k
    void submul(const rational & c, const inf_rational & k) {
        m_first.submul(c, k.m_first);
        m_second.submul(c, k.m_second);
    }
};

inline bool operator!=(const inf_rational & r1, const inf_rational & r2) { 
    return !operator==(r1, r2); 
}

inline bool operator!=(const rational & r1, const inf_rational & r2) { 
    return !operator==(r1, r2); 
}

inline bool operator!=(const inf_rational & r1, const rational & r2) { 
    return !operator==(r1, r2); 
}

inline bool operator>(const inf_rational & r1, const inf_rational & r2) { 
    return operator<(r2, r1); 
}

inline bool operator>(const inf_rational & r1, const rational & r2) { 
    return operator<(r2, r1); 
}

inline bool operator>(const rational & r1, const inf_rational & r2) { 
    return operator<(r2, r1); 
}

inline bool operator<=(const inf_rational & r1, const inf_rational & r2) { 
    return !operator>(r1, r2); 
}

inline bool operator<=(const rational & r1, const inf_rational & r2) { 
    return !operator>(r1, r2); 
}

inline bool operator<=(const inf_rational & r1, const rational & r2) { 
    return !operator>(r1, r2); 
}

inline bool operator>=(const inf_rational & r1, const inf_rational & r2) { 
    return !operator<(r1, r2); 
}

inline bool operator>=(const rational & r1, const inf_rational & r2) { 
    return !operator<(r1, r2); 
}

inline bool operator>=(const inf_rational & r1, const rational & r2) { 
    return !operator<(r1, r2); 
}

inline inf_rational operator+(const inf_rational & r1, const inf_rational & r2) { 
    return inf_rational(r1) += r2; 
}

inline inf_rational operator-(const inf_rational & r1, const inf_rational & r2) { 
    return inf_rational(r1) -= r2; 
}

inline inf_rational operator-(const inf_rational & r) { 
    inf_rational result(r); 
    result.neg(); 
    return result; 
}

inline inf_rational operator*(const rational & r1, const inf_rational & r2) {
    inf_rational result(r2);
    result.m_first  *= r1;
    result.m_second *= r1;
    return result;
}

inline inf_rational operator*(const inf_rational & r1, const rational & r2) {
    return r2 * r1;
}

inline inf_rational operator/(const inf_rational & r1, const rational & r2) {
    inf_rational result(r1);
    result.m_first  /= r2;
    result.m_second /= r2;
    return result;
}

#if 0
inf_rational inf_mult(inf_rational const& r1, inf_rational const& r2);
inf_rational sup_mult(inf_rational const& r1, inf_rational const& r2);

inf_rational inf_div(inf_rational const& r1, inf_rational const& r2);
inf_rational sup_div(inf_rational const& r1, inf_rational const& r2);

inf_rational inf_power(inf_rational const& r1, unsigned n);
inf_rational sup_power(inf_rational const& r1, unsigned n);

inf_rational inf_root(inf_rational const& r1, unsigned n);
inf_rational sup_root(inf_rational const& r1, unsigned n);
#endif
//
// inline inf_rational operator/(const inf_rational & r1, const inf_rational & r2)
// inline inf_rational operator%(const inf_rational & r1, const inf_rational & r2)
// inf_rational gcd(const inf_rational & r1, const inf_rational & r2);
// inf_rational lcm(const inf_rational & r1, const inf_rational & r2);

inline std::ostream & operator<<(std::ostream & target, const inf_rational & r)
{
    target << r.to_string();
    return target;
}


inline inf_rational abs(const inf_rational & r) {
    inf_rational result(r);
    if (result.is_neg()) {
        result.neg();
    }
    return result;
}

#endif /* INF_RATIONAL_H_ */
