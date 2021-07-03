#pragma once

#include "util/util.h"

class u256 {
    uint64_t m_num[4];
public:
    u256();
    u256(uint64_t n);
    u256(uint64_t const* v);
    u256 operator*(u256 const& other) const;
    u256 operator+(u256 const& other) const;
    u256 operator-(u256 const& other) const;
    u256& operator+=(u256 const& other);
    u256& operator*=(u256 const& other);
    u256& operator-=(u256 const& other);
};
