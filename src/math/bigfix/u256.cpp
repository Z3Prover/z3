#include "math/bigfix/u256.h"
#include "math/bigfix/Hacl_Bignum256.h"

u256 u256::operator*(u256 const& other) const {
    uint64_t result[8];
    Hacl_Bignum256_mul(const_cast<uint64_t*>(m_num), const_cast<uint64_t*>(other.m_num), result);
    return u256(result);
}
