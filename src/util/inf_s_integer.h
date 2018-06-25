/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    inf_s_integer.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2007-06-11.

Revision History:

--*/
#ifndef INF_S_INTEGER_H_
#define INF_S_INTEGER_H_

#include "util/s_integer.h"
#include "util/rational.h"

class inf_s_integer {
    static inf_s_integer m_zero;
    static inf_s_integer m_one;
    static inf_s_integer m_minus_one;
    int m_first;
    int m_second;
 public:

    unsigned hash() const { 
        return m_first ^ (m_second + 1);
    }

    struct hash_proc {  unsigned operator()(inf_s_integer const& r) const { return r.hash(); }  };

    struct eq_proc { bool operator()(inf_s_integer const& r1, inf_s_integer const& r2) const { return r1 == r2; } };

    void swap(inf_s_integer & n) { 
        std::swap(m_first, n.m_first);
        std::swap(m_second, n.m_second);
    }

    std::string to_string() const;

    inf_s_integer():m_first(0), m_second(0) {}

    inf_s_integer(const inf_s_integer & r):m_first(r.m_first), m_second(r.m_second) {}

    explicit inf_s_integer(int n):m_first(n), m_second(0) {}
    explicit inf_s_integer(int n, int d): m_first(n), m_second(0) { SASSERT(d == 1); }
    explicit inf_s_integer(s_integer const& r, bool pos_inf):m_first(r.get_int()), m_second(pos_inf ? 1 : -1) {}
    explicit inf_s_integer(s_integer const& r):m_first(r.get_int()), m_second(0) {}
    explicit inf_s_integer(rational const& r):m_first(static_cast<int>(r.get_int64())), m_second(0) {}
    inf_s_integer(s_integer const& r, s_integer const& i):m_first(r.get_int()), m_second(i.get_int()) {}
    void reset() { m_first = 0; m_second = 0; }
    bool is_int() const { return m_second == 0; } 
    bool is_int64() const { return m_second == 0; }
    bool is_uint64() const { return m_second == 0; }
    bool is_rational() const { return m_second == 0; }
    int64_t get_int64() const { return m_first; }
    uint64_t get_uint64() const { return m_first; }
    s_integer get_rational() const { return s_integer(m_first); }
    s_integer get_infinitesimal() const { return s_integer(m_second); }
    inf_s_integer & operator=(const inf_s_integer & r) { 
        m_first = r.m_first;
        m_second = r.m_second;
        return *this;
    }
    inf_s_integer & operator=(const rational & r) {
        m_first = static_cast<int>(r.get_int64());
        m_second = 0;
        return *this;
    }
    inf_s_integer & operator=(const s_integer & r) {
        m_first = r.get_int();
        m_second = 0;
        return *this;
    }
    friend inline inf_s_integer numerator(const inf_s_integer & r) {
        SASSERT(r.m_second == 0);
        return inf_s_integer(r.m_first);
    }
    friend inline inf_s_integer denominator(const inf_s_integer & r) {
        SASSERT(r.m_second == 0);
        return inf_s_integer(1);
    }
    inf_s_integer & operator+=(const inf_s_integer & r) { 
        m_first  += r.m_first;
        m_second += r.m_second;
        return *this; 
    }
    inf_s_integer & operator-=(const inf_s_integer & r) { 
        m_first  -= r.m_first;
        m_second -= r.m_second;
        return *this; 
    }
    inf_s_integer & operator+=(const s_integer & r) { 
        m_first  += r.get_int();
        return *this; 
    }
    inf_s_integer & operator-=(const s_integer & r) { 
        m_first  -= r.get_int();
        return *this; 
    }
    inf_s_integer & operator*=(const s_integer & r1) {
        m_first  *= r1.get_int();
        m_second *= r1.get_int();
        return *this;
    }
    
//     friend inf_s_integer inf_mult(inf_s_integer const& r1, inf_s_integer const& r2);
//     friend inf_s_integer sup_mult(inf_s_integer const& r1, inf_s_integer const& r2);

//     friend inf_s_integer inf_div(inf_s_integer const& r1, inf_s_integer const& r2);
//     friend inf_s_integer sup_div(inf_s_integer const& r1, inf_s_integer const& r2);

//     friend inf_s_integer inf_power(inf_s_integer const& r1, unsigned n);
//     friend inf_s_integer sup_power(inf_s_integer const& r1, unsigned n);

//     friend inf_s_integer inf_root(inf_s_integer const& r1, unsigned n);
//     friend inf_s_integer sup_root(inf_s_integer const& r1, unsigned n);

    inf_s_integer & operator/=(const s_integer & r) {
        m_first /= r.get_int();
        m_second /= r.get_int();
        return *this;
    }

    friend inline inf_s_integer operator*(const s_integer & r1, const inf_s_integer & r2);
    friend inline inf_s_integer operator/(const inf_s_integer & r1, const s_integer & r2);

    inf_s_integer & operator++() {
        ++m_first;
        return *this;
    }

    const inf_s_integer operator++(int) { inf_s_integer tmp(*this); ++(*this); return tmp; }
  
    inf_s_integer & operator--() {
        --m_first;
        return *this;
    }

    const inf_s_integer operator--(int) { inf_s_integer tmp(*this); --(*this); return tmp; }

    friend inline bool operator==(const inf_s_integer & r1, const inf_s_integer & r2) {
        return r1.m_first == r2.m_first && r1.m_second == r2.m_second;
    }

    friend inline bool operator==(const s_integer & r1, const inf_s_integer & r2) {
        return r1.get_int() == r2.m_first && r2.m_second == 0;
    }

    friend inline bool operator==(const inf_s_integer & r1, const s_integer & r2) {
        return r1.m_first == r2.get_int() && r1.m_second == 0;
    }

    friend inline bool operator<(const inf_s_integer & r1, const inf_s_integer & r2) { 
        return 
            (r1.m_first < r2.m_first) ||
            (r1.m_first == r2.m_first && r1.m_second < r2.m_second);
    }

    friend inline bool operator<(const s_integer & r1, const inf_s_integer & r2) { 
        return 
            (r1.get_int() < r2.m_first) ||
            (r1.get_int() == r2.m_first && r2.m_second > 0);
    }

    friend inline bool operator<(const inf_s_integer & r1, const s_integer & r2) { 
        return 
            (r1.m_first < r2.get_int()) ||
            (r1.m_first == r2.get_int() && r1.m_second < 0);
    }

    void neg() {
        m_first  = -m_first;
        m_second = -m_second;
    }

    bool is_zero() const {
        return m_first == 0 && m_second == 0;
    }

    bool is_one() const {
        return m_first == 1 && m_second == 0;
    }

    bool is_minus_one() const {
        return m_first == -1 && m_second == 0;
    }

    bool is_neg() const {
        return m_first < 0 || (m_first == 0 && m_second < 0);
    }
    
    bool is_pos() const {
        return m_first > 0 || (m_first == 0 && m_second > 0);
    }

    bool is_nonneg() const {
        return m_first > 0 || (m_first == 0 && m_second >= 0);
    }

    bool is_nonpos() const {
        return m_first < 0 || (m_first == 0 && m_second <= 0);
    }

    friend inline s_integer floor(const inf_s_integer & r) {
        if (r.m_second >= 0) {
            return s_integer(r.m_first);
        }
        return s_integer(r.m_first - 1);
    }

    friend inline s_integer ceil(const inf_s_integer & r) {
        if (r.m_second <= 0) {
            return s_integer(r.m_first);
        }
        return s_integer(r.m_first + 1);
    }

    static const inf_s_integer & zero() {
        return m_zero;
    }

    static const inf_s_integer & one() {
        return m_one;
    }

    static const inf_s_integer & minus_one() {
        return m_minus_one;
    }

    // Perform: this += c * k
    void addmul(const s_integer & c, const inf_s_integer & k) {
        m_first   += c.get_int() * k.m_first;
        m_second  += c.get_int() * k.m_second;
    }

    // Perform: this += c * k
    void submul(const s_integer & c, const inf_s_integer & k) {
        m_first   -= c.get_int() * k.m_first;
        m_second  -= c.get_int() * k.m_second;
    }

    friend inline std::ostream & operator<<(std::ostream & target, const inf_s_integer & r) {
        if (r.m_second == 0) {
            target << r.m_first;
        }
        else if (r.m_second < 0) {
            target << "(" << r.m_first << " -e*" << r.m_second << ")";
        }
        else {
            target << "(" << r.m_first << " +e*" << r.m_second << ")";
        }
        return target;
    }

};

inline bool operator!=(const inf_s_integer & r1, const inf_s_integer & r2) { 
    return !operator==(r1, r2); 
}

inline bool operator!=(const s_integer & r1, const inf_s_integer & r2) { 
    return !operator==(r1, r2); 
}

inline bool operator!=(const inf_s_integer & r1, const s_integer & r2) { 
    return !operator==(r1, r2); 
}

inline bool operator>(const inf_s_integer & r1, const inf_s_integer & r2) { 
    return operator<(r2, r1); 
}

inline bool operator>(const inf_s_integer & r1, const s_integer & r2) { 
    return operator<(r2, r1); 
}

inline bool operator>(const s_integer & r1, const inf_s_integer & r2) { 
    return operator<(r2, r1); 
}

inline bool operator<=(const inf_s_integer & r1, const inf_s_integer & r2) { 
    return !operator>(r1, r2); 
}

inline bool operator<=(const s_integer & r1, const inf_s_integer & r2) { 
    return !operator>(r1, r2); 
}

inline bool operator<=(const inf_s_integer & r1, const s_integer & r2) { 
    return !operator>(r1, r2); 
}

inline bool operator>=(const inf_s_integer & r1, const inf_s_integer & r2) { 
    return !operator<(r1, r2); 
}

inline bool operator>=(const s_integer & r1, const inf_s_integer & r2) { 
    return !operator<(r1, r2); 
}

inline bool operator>=(const inf_s_integer & r1, const s_integer & r2) { 
    return !operator<(r1, r2); 
}

inline inf_s_integer operator+(const inf_s_integer & r1, const inf_s_integer & r2) { 
    return inf_s_integer(r1) += r2; 
}

inline inf_s_integer operator-(const inf_s_integer & r1, const inf_s_integer & r2) { 
    return inf_s_integer(r1) -= r2; 
}

inline inf_s_integer operator-(const inf_s_integer & r) { 
    inf_s_integer result(r); 
    result.neg(); 
    return result; 
}

inline inf_s_integer operator*(const s_integer & r1, const inf_s_integer & r2) {
    inf_s_integer result(r2);
    result.m_first  *= r1.get_int();
    result.m_second *= r1.get_int();
    return result;
}

inline inf_s_integer operator/(const inf_s_integer & r1, const s_integer & r2) {
    inf_s_integer result(r1);
    result.m_first  /= r2.get_int();
    result.m_second /= r2.get_int();
    return result;
}

inline inf_s_integer abs(const inf_s_integer & r) {
    inf_s_integer result(r);
    if (result.is_neg()) {
        result.neg();
    }
    return result;
}


#endif /* INF_S_INTEGER_H_ */

