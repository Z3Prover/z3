#include "util/mpn.h"
#include "math/bigfix/u128.h"
#include "math/bigfix/Hacl_Bignum256.h"
#include <memory>

#if 0

u128::u128() {
    NOT_IMPLEMENTED_YET();
    // m_num = 0;
}

u128::u128(uint64_t n) {
    NOT_IMPLEMENTED_YET();
//    m_num = n;
}

u128::u128(int n) {
    NOT_IMPLEMENTED_YET();
    SASSERT(n >= 0);
//    m_num = n;
}

u128::u128(rational const& n) {
    NOT_IMPLEMENTED_YET();
#if 0
    for (unsigned i = 0; i < 2; ++i) {
        m_num[i] = 0;
        for (unsigned j = 0; j < 64; ++j)
            m_num[i] |= n.get_bit(i * 64 + j) << j;
    }
#endif
}


u128::u128(uint64_t const* v) {
    std::uninitialized_copy(v, v + 2, m_num);
}

u128 u128::operator*(u128 const& other) const {
    NOT_IMPLEMENTED_YET();   
    return u128();
}

u128 u128::operator<<(uint64_t sh) const {
    u128 r;
    NOT_IMPLEMENTED_YET();
    // TODO
    return r;
}

u128 u128::operator>>(uint64_t sh) const {
    u128 r;
    NOT_IMPLEMENTED_YET();
    // TODO
    return r;
}

u128 u128::operator&(u128 const& other) const {
    u128 r;
    NOT_IMPLEMENTED_YET();
    // TODO
    return r;
}

u128& u128::operator*=(u128 const& other) {
    NOT_IMPLEMENTED_YET();
    // TODO
    return *this;
}

u128& u128::operator+=(u128 const& other) {
    // TODO
    NOT_IMPLEMENTED_YET();
    return *this;
}

u128& u128::operator-=(u128 const& other) {
    // TODO
    NOT_IMPLEMENTED_YET();
    return *this;
}

u128& u128::uminus() {
    // TODO
    NOT_IMPLEMENTED_YET();
    return *this;    
}

u128 u128::mod(u128 const& other) const {
    if (other.is_zero())
        throw default_exception("mod 0 is not defined");
    if (other.is_one())
        return u128();

    // TODO

    u128 r;
    uint64_t a[8];
    a[4] = a[5] = a[6] = a[7] = 0;
    NOT_IMPLEMENTED_YET();

    if (!other.is_even()) {
        // std::uninitialized_copy(m_num, m_num + 4, a);
        // VERIFY(Hacl_Bignum256_mod(const_cast<uint64_t*>(other.m_num), a, r.m_num));
        return r;
    }
    
    // claim:
    // a mod 2^k*b = ((a >> k) mod b) << k | (a & ((1 << k) - 1))
    
    unsigned tz = other.trailing_zeros();
    u128 thz = *this >> tz;
    u128 n = other >> tz;
    SASSERT(!n.is_even() && n > 1);
    // std::uninitialized_copy(thz.m_num, thz.m_num + 4, a);
    // VERIFY(Hacl_Bignum256_mod(const_cast<uint64_t*>(n.m_num), a, r.m_num));
    r = r << tz;    
    r += *this & ((u128(1) << tz) - 1);
    return r;
}

u128 u128::mul_inverse() const {
    if (is_zero())
        return *this;
    if (is_one())
        return *this;
    if (is_even()) 
        return (*this >> trailing_zeros()).mul_inverse();

    u128 t0(1);
    u128 t1(-t0);
    u128 r0(*this);
    u128 r1(-r0); 
    while (!r1.is_zero()) {
        u128 q = r0 / r1;
        u128 tmp = t1;
        t1 = t0 - q * t1;
        t0 = tmp;
        tmp = r1;
        r1 = r0 - q * r1;
        r0 = tmp;
    }
    return t0;
}

unsigned u128::trailing_zeros() const {
    unsigned r = 0;
    // TODO
    return r;
}

u128 u128::gcd(u128 const& other) const {
    if (is_zero())
        return other;
    if (other.is_zero())
        return *this;
    if (is_one())
        return *this;
    if (other.is_one())
        return other;
    u128 x = *this;
    u128 y = other;
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


bool u128::operator<(uint64_t other) const {
    // TODO
    NOT_IMPLEMENTED_YET();
    return false;
}

bool u128::operator>(uint64_t other) const {
    // TODO
    NOT_IMPLEMENTED_YET();
    return false;
}

rational u128::to_rational() const {
    rational n;
    // TODO
    NOT_IMPLEMENTED_YET();
    return n;
}

std::ostream& u128::display(std::ostream& out) const {
    return out << to_rational();
}

// mpn implements the main functionality needed for unsigned fixed-point arithmetic
// we could use mpn for add/sub/mul as well and maybe punt on Hacl dependency.

u128 u128::operator/(u128 const& other) const {
    u128 result;
    // TODO
    NOT_IMPLEMENTED_YET();
    return result;
}

#endif