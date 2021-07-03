#pragma once

#include "util/util.h"
#include "util/rational.h"

class u256 {
    uint64_t m_num[4];
    u256(uint64_t const* v);
public:
    u256();
    u256(uint64_t n);
    u256(rational const& n);
    u256 operator*(u256 const& other) const;
    u256 operator+(u256 const& other) const { u256 r = *this; return r += other; }
    u256 operator-(u256 const& other) const { u256 r = *this; return r -= other; }
    u256 operator-() const { u256 r = *this; return r.inv(); }

    u256 mul_inverse() const;
    unsigned trailing_zeros() const;
    u256 gcd(u256 const& other) const;

    // updates
    void reset() { m_num[0] = m_num[1] = m_num[2] = m_num[3] = 0; }
    u256& operator+=(u256 const& other);
    u256& operator*=(u256 const& other);
    u256& operator-=(u256 const& other);
    u256& inv();  /* unary minus */

    // comparisons
    bool operator==(u256 const& other) const;
    bool operator!=(u256 const& other) const;
    bool operator<(u256 const& other) const;
    bool operator<=(u256 const& other) const;
    bool operator>(u256 const& other) const;
    bool operator>=(u256 const& other) const;

    bool operator<(uint64_t other) const;
    bool operator<=(uint64_t other) const;
    bool operator>(uint64_t other) const;
    bool operator>=(uint64_t other) const;

    bool is_zero() const { return m_num[0] == 0 && m_num[1] == 0 && m_num[2] == 0 && m_num[3] == 0; }
    bool is_one() const { return m_num[0] == 1 && m_num[1] == 0 && m_num[2] == 0 && m_num[3] == 0; }
    bool is_even() const { return (m_num[0]&1) == 0; }

    std::ostream& display(std::ostream& out) const;
    
};

inline std::ostream& operator<<(std::ostream& out, u256 const& u) {
    return u.display(out);
}
