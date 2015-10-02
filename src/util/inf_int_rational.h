/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    inf_int_rational.h

Abstract:

    Rational numbers with infenitesimals

Author:

    Leonardo de Moura (leonardo) 2006-09-18.
    Nikolaj Bjorner (nbjorner) 2006-10-24.

Revision History:

--*/
#ifndef INF_INT_RATIONAL_H_
#define INF_INT_RATIONAL_H_
#include<stdlib.h>
#include<string>
#include"debug.h"
#include"vector.h"
#include"rational.h"


class inf_int_rational {
    static inf_int_rational m_zero;
    static inf_int_rational m_one;
    static inf_int_rational m_minus_one;
    rational m_first;
    int      m_second;
 public:
    static void init(); // called from rational::initialize() only
    static void finalize();  // called from rational::finalize() only

    unsigned hash() const { 
        return m_first.hash() ^ (static_cast<unsigned>(m_second) + 1);
    }

    struct hash_proc {  unsigned operator()(inf_int_rational const& r) const { return r.hash(); }  };

    struct eq_proc { bool operator()(inf_int_rational const& r1, inf_int_rational const& r2) const { return r1 == r2; } };

    void swap(inf_int_rational & n) { 
        m_first.swap(n.m_first);
        std::swap(m_second, n.m_second);
    }

    std::string to_string() const;

    inf_int_rational():
        m_first(rational()),
        m_second(0)
     {}

    inf_int_rational(const inf_int_rational & r): 
        m_first(r.m_first),
        m_second(r.m_second)
     {}

    explicit inf_int_rational(int n):
        m_first(rational(n)),
        m_second(0)
    {}

    explicit inf_int_rational(int n, int d):
        m_first(rational(n,d)),
        m_second(0)
    {}

    explicit inf_int_rational(rational const& r, bool pos_inf):
        m_first(r),
        m_second(pos_inf?1:-1)
    {}

    explicit inf_int_rational(rational const& r):
        m_first(r),
        m_second(0) {}

    inf_int_rational(rational const& r, int i):
        m_first(r),
        m_second(i) {
    }

    ~inf_int_rational() {}

    /**
       \brief Set inf_int_rational to 0.
    */
    void reset() {
        m_first.reset();
        m_second = 0;
    }

    bool is_int() const { 
        return m_first.is_int() && m_second == 0;
    }

    bool is_int64() const { 
        return m_first.is_int64() && m_second == 0;
    }

    bool is_uint64() const { 
        return m_first.is_uint64() && m_second == 0;
    }

    bool is_rational() const { return m_second == 0; }

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

    rational get_infinitesimal() const {
        return rational(m_second);
    }

    rational const & get_first() const { return m_first; }

    inf_int_rational & operator=(const inf_int_rational & r) {
        m_first = r.m_first;
        m_second = r.m_second;
	return *this;
    }

    inf_int_rational & operator=(const rational & r) {
        m_first = r;
        m_second = 0;
        return *this;
    }

    friend inline inf_int_rational numerator(const inf_int_rational & r) {
        SASSERT(r.m_second == 0);
        return inf_int_rational(numerator(r.m_first));
    }

    friend inline inf_int_rational denominator(const inf_int_rational & r) {
        SASSERT(r.m_second == 0);
        return inf_int_rational(denominator(r.m_first));
    }

    inf_int_rational & operator+=(const inf_int_rational & r) { 
        m_first  += r.m_first;
        m_second += r.m_second;
	return *this; 
    }

    inf_int_rational & operator*=(const rational & r) { 
        if (!r.is_int32()) {
            throw default_exception("multiplication with large rational is not possible");
        }
        m_first  *= r;
        m_second *= r.get_int32();
	return *this; 
    }



    inf_int_rational & operator-=(const inf_int_rational & r) { 
        m_first  -= r.m_first;
        m_second -= r.m_second;
	return *this; 
    }

    inf_int_rational & operator+=(const rational & r) { 
        m_first  += r;
	return *this; 
    }

    inf_int_rational & operator-=(const rational & r) { 
        m_first  -= r;
	return *this; 
    }

    inf_int_rational & operator++() {
        ++m_first;
        return *this;
    }

    const inf_int_rational operator++(int) { inf_int_rational tmp(*this); ++(*this); return tmp; }
  
    inf_int_rational & operator--() {
        --m_first;
        return *this;
    }

    const inf_int_rational operator--(int) { inf_int_rational tmp(*this); --(*this); return tmp; }

    friend inline bool operator==(const inf_int_rational & r1, const inf_int_rational & r2) {
        return r1.m_first == r2.m_first && r1.m_second == r2.m_second;
    }

    friend inline bool operator==(const rational & r1, const inf_int_rational & r2) {
        return r1 == r2.m_first && r2.m_second == 0;
    }

    friend inline bool operator==(const inf_int_rational & r1, const rational & r2) {
        return r1.m_first == r2 && r1.m_second == 0;
    }

    friend inline bool operator<(const inf_int_rational & r1, const inf_int_rational & r2) { 
        return 
            (r1.m_first < r2.m_first) ||
            (r1.m_first == r2.m_first && r1.m_second < r2.m_second);
    }

    friend inline bool operator<(const rational & r1, const inf_int_rational & r2) { 
        return 
            (r1 < r2.m_first) ||
            (r1 == r2.m_first && r2.m_second > 0);
    }

    friend inline bool operator<(const inf_int_rational & r1, const rational & r2) { 
        return 
            (r1.m_first < r2) ||
            (r1.m_first == r2 && r1.m_second < 0);
    }

    void neg() {
        m_first.neg();
        m_second = -m_second;
    }

    bool is_zero() const {
        return m_first.is_zero() && m_second == 0;
    }

    bool is_one() const {
        return m_first.is_one() && m_second == 0;
    }

    bool is_minus_one() const {
        return m_first.is_minus_one() && m_second == 0;
    }

    bool is_neg() const {
        return 
            m_first.is_neg() || 
            (m_first.is_zero() && m_second < 0);
    }
    
    bool is_pos() const {
        return 
            m_first.is_pos() || 
            (m_first.is_zero() && m_second > 0);
    }

    bool is_nonneg() const {
        return 
            m_first.is_pos() ||
            (m_first.is_zero() && m_second >= 0);
    }

    bool is_nonpos() const {
        return 
            m_first.is_neg() ||
            (m_first.is_zero() && m_second <= 0);
    }

    friend inline rational floor(const inf_int_rational & r) {
        if (r.m_first.is_int()) {
            if (r.m_second >= 0) {
                return r.m_first;
            }
            return r.m_first - rational::one();
        }
        
        return floor(r.m_first);
    }

    friend inline rational ceil(const inf_int_rational & r) {
        if (r.m_first.is_int()) {
            if (r.m_second <= 0) {
                return r.m_first;
            }
            return r.m_first + rational::one();
        }
        
        return ceil(r.m_first);
    }

    static const inf_int_rational & zero() {
        return m_zero;
    }

    static const inf_int_rational & one() {
        return m_one;
    }

    static const inf_int_rational & minus_one() {
        return m_minus_one;
    }

};

inline bool operator!=(const inf_int_rational & r1, const inf_int_rational & r2) { 
    return !operator==(r1, r2); 
}

inline bool operator!=(const rational & r1, const inf_int_rational & r2) { 
    return !operator==(r1, r2); 
}

inline bool operator!=(const inf_int_rational & r1, const rational & r2) { 
    return !operator==(r1, r2); 
}

inline bool operator>(const inf_int_rational & r1, const inf_int_rational & r2) { 
    return operator<(r2, r1); 
}

inline bool operator>(const inf_int_rational & r1, const rational & r2) { 
    return operator<(r2, r1); 
}

inline bool operator>(const rational & r1, const inf_int_rational & r2) { 
    return operator<(r2, r1); 
}

inline bool operator<=(const inf_int_rational & r1, const inf_int_rational & r2) { 
    return !operator>(r1, r2); 
}

inline bool operator<=(const rational & r1, const inf_int_rational & r2) { 
    return !operator>(r1, r2); 
}

inline bool operator<=(const inf_int_rational & r1, const rational & r2) { 
    return !operator>(r1, r2); 
}

inline bool operator>=(const inf_int_rational & r1, const inf_int_rational & r2) { 
    return !operator<(r1, r2); 
}

inline bool operator>=(const rational & r1, const inf_int_rational & r2) { 
    return !operator<(r1, r2); 
}

inline bool operator>=(const inf_int_rational & r1, const rational & r2) { 
    return !operator<(r1, r2); 
}

inline inf_int_rational operator+(const inf_int_rational & r1, const inf_int_rational & r2) { 
    return inf_int_rational(r1) += r2; 
}

inline inf_int_rational operator*(const rational & r1, const inf_int_rational & r2) { 
    return inf_int_rational(r2) *= r1;
}

inline inf_int_rational operator-(const inf_int_rational & r1, const inf_int_rational & r2) { 
    return inf_int_rational(r1) -= r2; 
}

inline inf_int_rational operator-(const inf_int_rational & r) { 
    inf_int_rational result(r); 
    result.neg(); 
    return result; 
}

inline std::ostream & operator<<(std::ostream & target, const inf_int_rational & r)
{
    target << r.to_string();
    return target;
}


inline inf_int_rational abs(const inf_int_rational & r) {
    inf_int_rational result(r);
    if (result.is_neg()) {
        result.neg();
    }
    return result;
}

#endif /* INF_INT_RATIONAL_H_ */
