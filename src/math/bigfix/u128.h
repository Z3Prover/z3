#pragma once

#include "util/util.h"
#include "util/rational.h"
#include "math/bigfix/FStar_UInt128.h"

#if 0
class u128 {
    FStar_UInt128_uint128 m_num;
    u128(uint64_t const* v);
public:
    u128();
    u128(uint64_t n);
    u128(int n);
    u128(rational const& n);
    rational to_rational() const;
    u128& operator=(uint64_t n) {
        *this = u128(n);
        return *this;
    }
    u128 operator*(u128 const& other) const;
    u128 operator+(u128 const& other) const { u128 r = *this; return r += other; }
    u128 operator-(u128 const& other) const { u128 r = *this; return r -= other; }
    u128 operator/(u128 const& other) const;
    u128 operator-() const { u128 r = *this; return r.uminus(); }
    u128 operator<<(uint64_t sh) const;
    u128 operator>>(uint64_t sh) const;
    u128 operator&(u128 const& other) const;

    u128 mod(u128 const& other) const;
    u128 mul_inverse() const;
    unsigned trailing_zeros() const;
    u128 gcd(u128 const& other) const;

    // updates
    void reset(); // { m_num = 0; }
    u128& operator+=(u128 const& other);
    u128& operator*=(u128 const& other);
    u128& operator-=(u128 const& other);
    u128& operator/=(u128 const& other) { *this = *this / other; return *this; }
    u128& operator>>=(uint64_t sh) { *this = *this >> sh; return *this; }
    u128& operator<<=(uint64_t sh) { *this = *this << sh; return *this; }
    u128& uminus();  /* unary minus */

    // comparisons
    bool operator==(u128 const& other) const { return FStar_UInt128_eq(m_num, other.m_num); }
    bool operator!=(u128 const& other) const { return !(*this == other); }
    bool operator<(u128 const& other) const { return FStar_UInt128_lt(m_num, other.m_num); }
    bool operator<=(u128 const& other) const { return !(other < *this); }
    bool operator>(u128 const& other) const { return other < *this; }
    bool operator>=(u128 const& other) const { return !(*this < other); }

    bool operator==(uint64_t other) const; // { return m_num == other; }
    bool operator!=(uint64_t other) const { return !(*this == other); }

    bool operator<(uint64_t other) const;
    bool operator<=(uint64_t other) const { return !(*this > other); }
    bool operator>(uint64_t other) const;
    bool operator>=(uint64_t other) const { return !(*this < other); }

    bool is_zero() const { return *this == 0; }
    bool is_one() const { return *this == 1; }
    bool is_even() const; //  { return (m_num & 1) == 0; }

    std::ostream& display(std::ostream& out) const;
    
};

inline std::ostream& operator<<(std::ostream& out, u128 const& u) {
    return u.display(out);
}

inline bool operator<(uint64_t n, u128 const& y) { return y > n; }
inline bool operator<=(uint64_t n, u128 const& y) { return y >= n; }
inline bool operator>(uint64_t n, u128 const& y) { return y < n; }
inline unsigned trailing_zeros(u128 const& n) { return n.trailing_zeros(); }
   
inline u128 operator-(uint64_t n, u128 const& y) { return u128(n) - y; }
inline bool operator>=(uint64_t n, u128 const& y) { return y <= n; }
inline rational to_rational(u128 const& x) { return x.to_rational(); }
#endif