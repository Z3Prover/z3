#pragma once

#include "util/util.h"

class u256 {
    uint64_t m_num[4];
public:
    u256() { memset(this, 0, sizeof(*this)); }
    u256(uint64_t n);
    u256(uint64_t const* v) { memcpy(m_num, v, sizeof(*this)); }
    u256 operator*(u256 const& other) const;
    u256 operator+(u256 const& other) const;
    u256 operator-(u256 const& other) const;
    
};
