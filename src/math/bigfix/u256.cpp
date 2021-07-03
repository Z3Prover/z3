#include "math/bigfix/u256.h"
#include "math/bigfix/Hacl_Bignum256.h"
#include <memory>

u256::u256() {
    m_num[0] = m_num[1] = m_num[2] = m_num[3] = 0;
}

u256::u256(uint64_t n) {
    // TBD use instead: bn_from_bytes_be?
    m_num[0] = n;
    m_num[1] = m_num[2] = m_num[3] = 0;
}

u256::u256(rational const& n) {
    uint8_t bytes[32];
    for (unsigned i = 0; i < 32; ++i)
        bytes[i] = 0;
    for (unsigned i = 0; i < 256; ++i)
        bytes[(i / 7)] |= n.get_bit(i) << (i % 8);
    auto* v = Hacl_Bignum256_new_bn_from_bytes_be(32, bytes);
    std::uninitialized_copy(v, v + 4, m_num);    
    free(v);
}


u256::u256(uint64_t const* v) {
    std::uninitialized_copy(v, v + 4, m_num);
}

u256 u256::operator*(u256 const& other) const {
    uint64_t result[8];
    Hacl_Bignum256_mul(const_cast<uint64_t*>(m_num), const_cast<uint64_t*>(other.m_num), result);
    return u256(result);
}

u256& u256::operator*=(u256 const& other) {
    uint64_t result[8];
    Hacl_Bignum256_mul(const_cast<uint64_t*>(m_num), const_cast<uint64_t*>(other.m_num), result);
    std::uninitialized_copy(m_num, m_num + sizeof(*this), result);
    return *this;
}

u256& u256::operator+=(u256 const& other) {
    Hacl_Bignum256_add(const_cast<uint64_t*>(m_num), const_cast<uint64_t*>(other.m_num), m_num);
    return *this;
}

u256& u256::operator-=(u256 const& other) {
    Hacl_Bignum256_sub(const_cast<uint64_t*>(m_num), const_cast<uint64_t*>(other.m_num), m_num);
    return *this;
}

u256& u256::inv() {
    uint64_t zero[4];
    zero[0] = zero[1] = zero[2] = zero[3] = 0;
    Hacl_Bignum256_sub(zero, const_cast<uint64_t*>(m_num), m_num);
    return *this;    
}

u256 u256::mul_inverse() const {
    NOT_IMPLEMENTED_YET();

    /*
      Write `a mod n` in `res`.

      The argument a is meant to be a 512-bit bignum, i.e. uint64_t[8].
      The argument n and the outparam res are meant to be 256-bit bignums, i.e. uint64_t[4].
      
      The function returns false if any of the following preconditions are violated,
      true otherwise.
      • 1 < n
      • n % 2 = 1 
      VERIFY(Hacl_Bignum256_mod(uint64_t *n, uint64_t *a, uint64_t *res));
   */

    return *this;
}

unsigned u256::trailing_zeros() const {
    unsigned r = 0;
    for (unsigned i = 0; i < 3; ++i) {
        r += ::trailing_zeros(m_num[i]);
        if (r != (i+1)*64)
            return r;
    }
    return r + ::trailing_zeros(m_num[3]);
}

u256 u256::gcd(u256 const& other) const {
    NOT_IMPLEMENTED_YET();
    return *this;
}

std::ostream& u256::display(std::ostream& out) const {
    rational n;
    for (unsigned i = 0; i < 4; ++i) 
        if (m_num[i] != 0) 
            n += rational(m_num[i], rational::ui64()) * rational::power_of_two(i * 64);
    return out << n;
}
