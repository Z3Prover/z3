#include "util/mpn.h"
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

u256::u256(int n) {
    SASSERT(n >= 0);
    m_num[0] = n;
    m_num[1] = m_num[2] = m_num[3] = 0;
}

u256::u256(rational const& n) {
#if 1
    for (unsigned i = 0; i < 4; ++i) {
        m_num[i] = 0;
        for (unsigned j = 0; j < 64; ++j)
            m_num[i] |= n.get_bit(i * 64 + j) << j;
    }
#else
    uint8_t bytes[32];
    for (unsigned i = 0; i < 32; ++i)
        bytes[i] = 0;
    for (unsigned i = 0; i < 256; ++i)
        bytes[(i / 7)] |= n.get_bit(i) << (i % 8);
    auto* v = Hacl_Bignum256_new_bn_from_bytes_be(32, bytes);
    std::uninitialized_copy(v, v + 4, m_num);    
    free(v);
#endif
}


u256::u256(uint64_t const* v) {
    std::uninitialized_copy(v, v + 4, m_num);
}

unsigned u256::hash() const {
    uint64_t h = m_num[0] + m_num[1] + m_num[2] + m_num[3];
    return static_cast<unsigned>(h ^ (h >> 32ull));
}

u256 u256::operator*(u256 const& other) const {
    // TBD: maybe just use mpn_manager::mul?
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

u256& u256::uminus() {
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
    
    // claim:
    // a mod 2^k*b = ((a >> k) mod b) << k | (a & ((1 << k) - 1))
    
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
    if (is_zero())
        return *this;
    if (is_one())
        return *this;
    if (is_even()) 
        return (*this >> trailing_zeros()).mul_inverse();

    u256 t0(1);
    u256 t1(-t0);
    u256 r0(*this);
    u256 r1(-r0); 
    while (!r1.is_zero()) {
        u256 q = r0 / r1;
        u256 tmp = t1;
        t1 = t0 - q * t1;
        t0 = tmp;
        tmp = r1;
        r1 = r0 - q * r1;
        r0 = tmp;
    }
    return t0;
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

rational u256::to_rational() const {
    rational n;
    for (unsigned i = 0; i < 4; ++i) 
        if (m_num[i] != 0) 
            n += rational(m_num[i], rational::ui64()) * rational::power_of_two(i * 64);
    return n;
}

std::ostream& u256::display(std::ostream& out) const {
    return out << to_rational();
}

// mpn implements the main functionality needed for unsigned fixed-point arithmetic
// we could use mpn for add/sub/mul as well and maybe punt on Hacl dependency.

u256 u256::operator/(u256 const& other) const {
    u256 result;
    mpn_manager m;
    mpn_digit rem[8];
    unsigned n1 = 0, n2 = 0;
    for (unsigned i = 4; i-- > 0; ) {
        if (m_num[i]) {
            n1 = 2 * (i + 1);
            break;
        }
    }
    for (unsigned i = 4; i-- > 0; ) {
        if (other.m_num[i]) {
            n2 = 2 * (i + 1);
            break;
        }
    }
    VERIFY(m.div(reinterpret_cast<mpn_digit const*>(m_num), n1,
        reinterpret_cast<mpn_digit const*>(other.m_num), n2,
        reinterpret_cast<mpn_digit*>(result.m_num),
        rem));
    return result;
}
