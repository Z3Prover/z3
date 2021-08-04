#pragma once

#include "util/util.h"
#include "util/rational.h"

class u256 {
    uint64_t m_num[4];
    u256(uint64_t const* v);
public:
    u256();
    u256(uint64_t n);
    u256(int n);
    u256(rational const& n);
    rational to_rational() const;
    u256& operator=(uint64_t n) {
        *this = u256(n);
        return *this;
    }
    u256 operator*(u256 const& other) const;
    u256 operator+(u256 const& other) const { u256 r = *this; return r += other; }
    u256 operator-(u256 const& other) const { u256 r = *this; return r -= other; }
    u256 operator/(u256 const& other) const;
    u256 operator-() const { u256 r = *this; return r.uminus(); }
    u256 operator<<(uint64_t sh) const;
    u256 operator>>(uint64_t sh) const;
    u256 operator&(u256 const& other) const;

    u256 mod(u256 const& other) const;
    u256 mul_inverse() const;
    unsigned trailing_zeros() const;
    u256 gcd(u256 const& other) const;

    // updates
    void reset() { m_num[0] = m_num[1] = m_num[2] = m_num[3] = 0; }
    u256& operator+=(u256 const& other);
    u256& operator*=(u256 const& other);
    u256& operator-=(u256 const& other);
    u256& operator/=(u256 const& other) { *this = *this / other; return *this; }
    u256& operator>>=(uint64_t sh) { *this = *this >> sh; return *this; }
    u256& operator<<=(uint64_t sh) { *this = *this << sh; return *this; }
    u256& uminus();  /* unary minus */

    // comparisons
    bool operator==(u256 const& other) const { return m_num[0] == other.m_num[0] && m_num[1] == other.m_num[1] && m_num[2] == other.m_num[2] && m_num[3] == other.m_num[3]; } 
    bool operator!=(u256 const& other) const { return !(*this == other); }
    bool operator<(u256 const& other) const;
    bool operator<=(u256 const& other) const { return !(other < *this); }
    bool operator>(u256 const& other) const { return other < *this; }
    bool operator>=(u256 const& other) const { return !(*this < other); }

    bool operator==(uint64_t other) const { return m_num[0] == other && m_num[1] == 0 && m_num[2] == 0 && m_num[3] == 0; }
    bool operator!=(uint64_t other) const { return !(m_num[0] == other && m_num[1] == 0 && m_num[2] == 0 && m_num[3] == 0); }
    bool operator<(uint64_t other) const;
    bool operator<=(uint64_t other) const { return !(*this > other); }
    bool operator>(uint64_t other) const;
    bool operator>=(uint64_t other) const { return !(*this < other); }

    bool is_zero() const { return m_num[0] == 0 && m_num[1] == 0 && m_num[2] == 0 && m_num[3] == 0; }
    bool is_one() const { return m_num[0] == 1 && m_num[1] == 0 && m_num[2] == 0 && m_num[3] == 0; }
    bool is_even() const { return (m_num[0]&1) == 0; }

    std::ostream& display(std::ostream& out) const;
    
};

inline std::ostream& operator<<(std::ostream& out, u256 const& u) {
    return u.display(out);
}

inline bool operator<(uint64_t n, u256 const& y) { return y > n; }
inline bool operator<=(uint64_t n, u256 const& y) { return y >= n; }
inline bool operator>(uint64_t n, u256 const& y) { return y < n; }
inline unsigned trailing_zeros(u256 const& n) {
    NOT_IMPLEMENTED_YET();
    return 0;
}
inline u256 operator-(uint64_t n, u256 const& y) {
    u256 x(n);
    return x - y;
}
inline bool operator>=(uint64_t n, u256 const& y) { return y <= n; }
