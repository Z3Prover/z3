/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    integer.h

Abstract:

    machine s_integer wrapper

Author:

    Leonardo de Moura (leonardo) 2007-06-01.

Revision History:

--*/
#ifndef S_INTEGER_H_
#define S_INTEGER_H_

#include "util/rational.h"

class s_integer {
    int m_val;
    static s_integer m_zero;
    static s_integer m_one;
    static s_integer m_minus_one;
public:

    unsigned hash() const { 
        return m_val;
    }

    struct hash_proc {  unsigned operator()(s_integer const& r) const { return r.hash(); }  };
    struct eq_proc { bool operator()(s_integer const& r1, s_integer const& r2) const { return r1 == r2; } };

    void swap(s_integer & n) { 
        std::swap(m_val, n.m_val);
    }

    std::string to_string() const;

public:
    s_integer(): m_val(0) {}
    s_integer(const s_integer & r):m_val(r.m_val) {}
    explicit s_integer(int n):m_val(n) {}
    struct i64 {};
    explicit s_integer(int64_t i, i64):m_val(static_cast<int>(i)) {}
    struct ui64 {};
    explicit s_integer(uint64_t i, ui64):m_val(static_cast<int>(i)) {}
    explicit s_integer(const char * str);
    explicit s_integer(const rational & r):m_val(static_cast<int>(r.get_int64())) {}

    void reset() { m_val = 0; }
    
    static bool is_big() { return false; }
    static bool is_int() { return true; }
    static bool is_s_integer() { return true; }
    static bool is_int64() { return true; }
    static bool is_uint64() { return true; }
    int get_int() const { return m_val; }
    int64_t get_int64() const { return m_val; }
    uint64_t get_uint64() const { return m_val; }
    static bool is_unsigned() { return true; }
    unsigned get_unsigned() const { return static_cast<unsigned>(m_val); }
    s_integer const& get_s_integer() const { return *this; }
    s_integer const& get_infinitesimal() const { return zero(); }
    static bool is_rational() { return true; }
    s_integer const& get_rational() const { return *this; } 
    s_integer & operator=(const s_integer & r) { m_val = r.m_val; return *this; }
    friend inline s_integer numerator(const s_integer & r) { return r; }
    friend inline s_integer denominator(const s_integer & r) { return one(); }
    s_integer & operator+=(const s_integer & r) { m_val += r.m_val; return *this; }
    s_integer & operator-=(const s_integer & r) { m_val -= r.m_val; return *this; }
    s_integer & operator*=(const s_integer & r) { m_val *= r.m_val; return *this; }
    s_integer & operator/=(const s_integer & r) { m_val /= r.m_val; return *this; }
    s_integer & operator%=(const s_integer & r) { m_val %= r.m_val; return *this; }
    friend inline s_integer div(const s_integer & r1, const s_integer & r2) { return s_integer(r1.m_val / r2.m_val); }
    friend inline s_integer mod(const s_integer & r1, const s_integer & r2) { 
        s_integer r = r1;
        r %= r2;
        if (r.is_neg()) {
            r += r2;
        }
        return r;
    }
    s_integer & operator++() { m_val++; return *this; }
    const s_integer operator++(int) { s_integer tmp(*this); ++(*this); return tmp; }
    s_integer & operator--() { m_val--; return *this; }
    const s_integer operator--(int) { s_integer tmp(*this); --(*this); return tmp; }
    friend inline bool operator==(const s_integer & r1, const s_integer & r2) { return r1.m_val == r2.m_val; }
    friend inline bool operator<(const s_integer & r1, const s_integer & r2) { return r1.m_val < r2.m_val; }
    void neg() { m_val = -m_val; }
    bool is_zero() const { return m_val == 0; }
    bool is_one() const { return m_val == 1; }
    bool is_minus_one() const { return m_val == -1; }
    bool is_neg() const { return m_val < 0; }
    bool is_pos() const { return m_val > 0; }
    bool is_nonneg() const {return m_val >= 0; }
    bool is_nonpos() const { return m_val <= 0; }
    bool is_even() const { return (!(m_val & 0x1)); }
    friend inline s_integer floor(const s_integer & r) { return r; }
    friend inline s_integer ceil(const s_integer & r) { return r; }
    s_integer expt(int n) const {
        s_integer result(1);
        for (int i = 0; i < n; i++) {
            result *= *this;
        }
        return result;
    }

    static const s_integer & zero() { return m_zero; }
    static const s_integer & one() { return m_one; }
    static const s_integer & minus_one() { return m_minus_one; }
    // Perform:  this += c * k
    void addmul(const s_integer & c, const s_integer & k) { m_val += c.m_val * k.m_val; }
    void submul(const s_integer & c, const s_integer & k) { m_val -= c.m_val * k.m_val; }
    friend inline std::ostream & operator<<(std::ostream & target, const s_integer & r) {
        target << r.m_val;
        return target;
    }

    rational to_rational() const { return rational(m_val); }
};

inline bool operator!=(const s_integer & r1, const s_integer & r2) { return !operator==(r1, r2); }
inline bool operator>(const s_integer & r1, const s_integer & r2) { return operator<(r2, r1); }
inline bool operator<=(const s_integer & r1, const s_integer & r2) { return !operator>(r1, r2); }
inline bool operator>=(const s_integer & r1, const s_integer & r2) { return !operator<(r1, r2); }
inline s_integer operator+(const s_integer & r1, const s_integer & r2) { return s_integer(r1) += r2; }
inline s_integer operator-(const s_integer & r1, const s_integer & r2) { return s_integer(r1) -= r2; }
inline s_integer operator-(const s_integer & r) { s_integer result(r); result.neg();  return result; }
inline s_integer operator*(const s_integer & r1, const s_integer & r2) { return s_integer(r1) *= r2; }
inline s_integer operator/(const s_integer & r1, const s_integer & r2) { return s_integer(r1) /= r2; }
inline s_integer operator%(const s_integer & r1, const s_integer & r2) { return s_integer(r1) %= r2; }
s_integer power(const s_integer & r, unsigned p);
s_integer gcd(const s_integer & r1, const s_integer & r2);
s_integer lcm(const s_integer & r1, const s_integer & r2);
inline s_integer abs(const s_integer & r) {
    s_integer result(r);
    if (result.is_neg()) {
        result.neg();
    }
    return result;
}

#endif /* S_INTEGER_H_ */

