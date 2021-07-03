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

u256 u256::operator<<(uint64_t sh) const {
    u256 r;
    if (0 == sh || sh >= 256) 
        ;
    else if (sh >= 176) 
        r.m_num[3] = m_num[0] << (sh - 176);
    else if (sh >= 128) {
        sh -= 128;
        r.m_num[2] = m_num[0] << sh;
        r.m_num[3] = (m_num[1] << sh) | (m_num[0] >> (64 - sh));
    }
    else if (sh >= 64) {
        sh -= 64;
        r.m_num[1] = m_num[0] << sh;
        r.m_num[2] = (m_num[1] << sh) | (m_num[0] >> (64 - sh));
        r.m_num[3] = (m_num[2] << sh) | (m_num[1] >> (64 - sh));
    }
    else {
        r.m_num[0] = m_num[0] << sh;
        r.m_num[1] = (m_num[1] << sh) | (m_num[0] >> (64 - sh));
        r.m_num[2] = (m_num[2] << sh) | (m_num[1] >> (64 - sh));
        r.m_num[3] = (m_num[3] << sh) | (m_num[2] >> (64 - sh));
    }
    return r;
}

u256 u256::operator>>(uint64_t sh) const {
    u256 r;
    if (0 == sh || sh >= 256) 
        ;
    else if (sh >= 176) 
        r.m_num[0] = m_num[3] >> (sh - 176);
    else if (sh >= 128) {
        sh -= 128;
        r.m_num[0] = (m_num[2] >> sh) | (m_num[3] << (64 - sh));
        r.m_num[1] = (m_num[3] >> sh);
    }
    else if (sh >= 64) {
        sh -= 64;
        r.m_num[0] = (m_num[1] >> sh) | (m_num[2] << (64 - sh));
        r.m_num[1] = (m_num[2] >> sh) | (m_num[3] << (64 - sh));
        r.m_num[2] = (m_num[3] >> sh);
    }
    else {
        r.m_num[0] = (m_num[0] >> sh) | (m_num[1] << (64 - sh));
        r.m_num[1] = (m_num[1] >> sh) | (m_num[2] << (64 - sh));
        r.m_num[2] = (m_num[2] >> sh) | (m_num[3] << (64 - sh));
        r.m_num[3] = (m_num[3] >> sh);
    }
    return r;
}

u256 u256::operator&(u256 const& other) const {
    u256 r;
    for (unsigned i = 0; i < 4; ++i) 
        r.m_num[i] = m_num[i] & other.m_num[i];
    return r;
}



u256& u256::operator*=(u256 const& other) {
    uint64_t result[8];
    Hacl_Bignum256_mul(const_cast<uint64_t*>(m_num), const_cast<uint64_t*>(other.m_num), result);
    std::uninitialized_copy(m_num, m_num + 4, result);
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

u256 u256::mod(u256 const& other) const {
    if (other.is_zero())
        throw default_exception("mod 0 is not defined");
    if (other.is_one())
        return u256();

    u256 r;
    uint64_t a[8];
    a[4] = a[5] = a[6] = a[7] = 0;

    if (!other.is_even()) {
        std::uninitialized_copy(m_num, m_num + 4, a);
        VERIFY(Hacl_Bignum256_mod(const_cast<uint64_t*>(other.m_num), a, r.m_num));
        return r;
    }
    unsigned tz = other.trailing_zeros();
    u256 thz = *this >> tz;
    u256 n = other >> tz;
    SASSERT(!n.is_even() && n > 1);
    std::uninitialized_copy(thz.m_num, thz.m_num + 4, a);
    VERIFY(Hacl_Bignum256_mod(const_cast<uint64_t*>(n.m_num), a, r.m_num));
    r = r << tz;    
    r += *this & ((u256(1) << tz) - 1);
    return r;
}

u256 u256::mul_inverse() const {
    NOT_IMPLEMENTED_YET();
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
    if (is_zero())
        return other;
    if (other.is_zero())
        return *this;
    if (is_one())
        return *this;
    if (other.is_one())
        return other;
    u256 x = *this;
    u256 y = other;
    unsigned tz = x.trailing_zeros();
    unsigned shift = std::min(y.trailing_zeros(), tz);
    x = x >> tz;
    if (x == 1) 
        return x << shift;
    if (y == 1) 
        return y << shift;
    if (x == y) 
        return x << shift;
    do {
        tz = y.trailing_zeros();
        y = y >> tz;
        if (x > y) 
            std::swap(x, y);
        y -= x;
    }
    while (!y.is_zero());
    return x << shift;
}


bool u256::operator<(u256 const& other) const {
    return 0 != Hacl_Bignum256_lt_mask(const_cast<uint64_t*>(m_num), const_cast<uint64_t*>(other.m_num));
}

bool u256::operator<(uint64_t other) const {
    uint64_t _other[4];
    _other[0] = other;
    _other[1] = _other[2] = _other[3] = 0;
    return 0 != Hacl_Bignum256_lt_mask(const_cast<uint64_t*>(m_num), _other);
}

bool u256::operator>(uint64_t other) const {
    uint64_t _other[4];
    _other[0] = other;
    _other[1] = _other[2] = _other[3] = 0;
    return 0 != Hacl_Bignum256_lt_mask(_other, const_cast<uint64_t*>(m_num));
}


std::ostream& u256::display(std::ostream& out) const {
    rational n;
    for (unsigned i = 0; i < 4; ++i) 
        if (m_num[i] != 0) 
            n += rational(m_num[i], rational::ui64()) * rational::power_of_two(i * 64);
    return out << n;
}
