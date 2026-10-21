/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    rational.cpp

Abstract:

    Rational numbers

Author:

    Leonardo de Moura (leonardo) 2006-09-18.

Revision History:

--*/
#include<sstream>
#include "util/mutex.h"
#include "util/util.h"
#include "util/rational.h"

synch_mpq_manager *  rational::g_mpq_manager = nullptr;
rational             rational::m_zero;
rational             rational::m_one;
rational             rational::m_minus_one;
vector<rational>     rational::m_powers_of_two;

void rational::release_large() noexcept {
    mpq* q = &large();
    synch_mpq_manager::del(g_mpq_manager, *q);
    dealloc(q);
}

void rational::set_fraction(int64_t n, uint64_t d) {
    SASSERT(d != 0);
    uint64_t magnitude = n < 0 ? uint64_t(0) - uint64_t(n) : uint64_t(n);
    uint64_t g = std::gcd(magnitude, d);
    magnitude /= g;
    uint64_t denominator = d / g;
    if (magnitude <= uint64_t(inline_limit) && denominator <= uint64_t(inline_limit)) {
        release();
        int32_t num = static_cast<int32_t>(magnitude);
        m_value = encode(n < 0 ? -num : num, static_cast<uint32_t>(denominator));
    }
    else {
        mpq_value q;
        m().set(q, n, d);
        set(std::move(q));
    }
}

void rational::set(mpq&& q) {
    if (m().is_int64(q.numerator()) && m().is_uint64(q.denominator())) {
        int64_t n = m().get_int64(q.numerator());
        uint64_t d = m().get_uint64(q.denominator());
        if (-inline_limit <= n && n <= inline_limit && d <= uint64_t(inline_limit)) {
            SASSERT(d != 0);
            release();
            m_value = encode(static_cast<int32_t>(n), static_cast<uint32_t>(d));
            synch_mpq_manager::del(g_mpq_manager, q);
            return;
        }
    }
    static_assert(alignof(mpq) >= 2);
    static_assert(sizeof(uintptr_t) <= sizeof(m_value));
    mpq* p = alloc(mpq, std::move(q));
    release();
    m_value = uint64_t(reinterpret_cast<uintptr_t>(p)) | 1;
}

void rational::compact() {
    SASSERT(!is_inline());
    mpq& q = large();
    if (m().is_int64(q.numerator()) && m().is_uint64(q.denominator())) {
        int64_t n = m().get_int64(q.numerator());
        uint64_t d = m().get_uint64(q.denominator());
        if (-inline_limit <= n && n <= inline_limit && d <= uint64_t(inline_limit)) {
            release();
            m_value = encode(static_cast<int32_t>(n), static_cast<uint32_t>(d));
        }
    }
}

rational::rational(uint64_t n) {
    if (n <= uint64_t(inline_limit))
        m_value = encode(static_cast<int32_t>(n), 1);
    else {
        mpq_value q;
        m().set(q, n);
        set(std::move(q));
    }
}

rational& rational::apply(rational const& r, binary_op op) {
    mpq_arg a(*this), b(r);
    mpq_value tmp;
    mpq& out = is_inline() ? static_cast<mpq&>(tmp) : large();
    switch (op) {
    case binary_op::add: m().add(a.get(), b.get(), out); break;
    case binary_op::sub: m().sub(a.get(), b.get(), out); break;
    case binary_op::mul: m().mul(a.get(), b.get(), out); break;
    case binary_op::div: m().div(a.get(), b.get(), out); break;
    case binary_op::rem: m().rem(a.get(), b.get(), out); break;
    }
    if (is_inline())
        set(std::move(tmp));
    else
        compact();
    return *this;
}

unsigned rational::bitsize() const {
    if (!is_inline()) return m().bitsize(large());
    unsigned n = static_cast<unsigned>(small_num() < 0 ? -small_num() : small_num());
    unsigned nb = std::max(1, std::bit_width(n));
    return is_int() ? nb : nb + std::bit_width(small_den());
}

unsigned rational::large_hash() const {
#ifdef _MP_GMP
    // GMP can retain a machine integer in a large mpz after cancellation.
    mpz const& num = large().numerator();
    if (m().is_int64(num)) {
        int64_t n = m().get_int64(num);
        if (INT_MIN <= n && n <= INT_MAX) {
            unsigned magnitude = n < 0 ? static_cast<unsigned>(-n) : static_cast<unsigned>(n);
            return magnitude + 3 * m().hash(large().denominator());
        }
    }
#endif
    return m().hash(large());
}

std::string rational::to_string() const {
    std::ostringstream out;
    display(out);
    return out.str();
}

void rational::display(std::ostream& out) const {
    if (!is_inline()) { m().display(out, large()); return; }
    out << small_num();
    if (small_den() != 1) out << '/' << small_den();
}

void rational::display_hex(std::ostream& out, unsigned num_bits) const {
    SASSERT(is_int());
    mpq_arg q(*this);
    m().display_hex(out, q.get().numerator(), num_bits);
}

void rational::display_bin(std::ostream& out, unsigned num_bits) const {
    SASSERT(is_int());
    mpq_arg q(*this);
    m().display_bin(out, q.get().numerator(), num_bits);
}

void rational::display_decimal(std::ostream& out, unsigned prec, bool truncate) const {
    mpq_arg q(*this);
    m().display_decimal(out, q.get(), prec, truncate);
}

void rational::display_smt2(std::ostream& out) const {
    mpq_arg q(*this);
    m().display_smt2(out, q.get(), false);
}

rational inv(rational const& r) {
    SASSERT(!r.is_zero());
    if (r.is_inline()) {
        rational result;
        int n = r.small_num();
        result.set(n < 0 ? -int64_t(r.small_den()) : int64_t(r.small_den()), n < 0 ? -n : n);
        return result;
    }
    rational::mpq_value out;
    rational::m().inv(r.large(), out);
    return rational(std::move(out));
}

rational div(rational const& a, rational const& b) {
    SASSERT(a.is_int() && b.is_int());
    if (a.is_inline() && b.is_inline() && !b.is_zero()) {
        int64_t n = a.small_num(), d = b.small_num();
        int64_t q = n / d;
        if (n % d < 0) q += d < 0 ? 1 : -1;
        return rational(q);
    }
    rational::mpq_arg av(a), bv(b);
    rational::mpq_value out;
    rational::m().idiv(av.get(), bv.get(), out);
    return rational(std::move(out));
}

rational machine_div(rational const& a, rational const& b) {
    SASSERT(a.is_int() && b.is_int());
    if (a.is_inline() && b.is_inline() && !b.is_zero())
        return rational(a.small_num() / b.small_num());
    rational::mpq_arg av(a), bv(b);
    rational::mpq_value out;
    rational::m().machine_idiv(av.get(), bv.get(), out);
    return rational(std::move(out));
}

rational machine_div_rem(rational const& a, rational const& b, rational& rem) {
    rational::mpq_arg av(a), bv(b);
    rational::mpq_value out, r;
    rational::m().machine_idiv_rem(av.get(), bv.get(), out, r);
    rational result(std::move(out));
    rem = rational(std::move(r));
    return result;
}

rational machine_div2k(rational const& a, unsigned k) {
    rational::mpq_arg av(a);
    rational::mpq_value out;
    rational::m().machine_idiv2k(av.get(), k, out);
    return rational(std::move(out));
}

rational mod(rational const& a, rational const& b) {
    SASSERT(a.is_int() && b.is_int());
    if (a.is_inline() && b.is_inline() && !b.is_zero()) {
        int n = a.small_num() % b.small_num();
        if (n < 0) n += b.small_num() < 0 ? -b.small_num() : b.small_num();
        return rational(n);
    }
    rational::mpq_arg av(a), bv(b);
    rational::mpq_value out;
    rational::m().mod(av.get(), bv.get(), out);
    return rational(std::move(out));
}

rational mod2k(rational const& a, unsigned k) {
    if (a.is_int()) {
        rational::mpq_arg av(a);
        return rational(rational::m().mod2k(av.get().numerator(), k));
    }
    return mod(a, rational::power_of_two(k));
}

rational floor(rational const& r) {
    if (r.is_inline()) {
        int64_t n = r.small_num(), d = r.small_den();
        return rational(n / d - (n % d < 0));
    }
    rational::mpq_value out;
    rational::m().floor(r.large(), out);
    return rational(std::move(out));
}

rational ceil(rational const& r) {
    if (r.is_inline()) {
        int64_t n = r.small_num(), d = r.small_den();
        return rational(n / d + (n % d > 0));
    }
    rational::mpq_value out;
    rational::m().ceil(r.large(), out);
    return rational(std::move(out));
}

rational rational::expt(int n) const {
    unsigned p = static_cast<unsigned>(n);
    if (!is_inline() || p > (1u << 20)) {
        mpq_arg q(*this);
        mpq_value out;
        m().power(q.get(), p, out);
        return rational(std::move(out));
    }
    rational result(1), base(*this);
    while (p) {
        if (p & 1) result *= base;
        p >>= 1;
        if (p) base *= base;
    }
    return result;
}

bool rational::is_power_of_two(unsigned& shift) const {
    if (!is_inline()) return m().is_power_of_two(large(), shift);
    if (!is_int() || small_num() <= 0 || !std::has_single_bit(uint32_t(small_num()))) return false;
    shift = std::countr_zero(uint32_t(small_num()));
    return true;
}

unsigned rational::prev_power_of_two() const {
    if (!is_inline()) return m().prev_power_of_two(large());
    mpq_arg q(*this);
    return m().prev_power_of_two(q.get());
}

unsigned rational::next_power_of_two() const {
    if (!is_inline()) return m().next_power_of_two(large());
    mpq_arg q(*this);
    return m().next_power_of_two(q.get());
}

bool rational::get_bit(unsigned index) const {
    if (is_inline() && is_int()) {
        SASSERT(!is_neg());
        return index < 32 && ((uint32_t(small_num()) >> index) & 1);
    }
    mpq_arg q(*this);
    return m().get_bit(q.get(), index);
}

bool rational::is_int_perfect_square(rational& root) const {
    mpq_arg q(*this);
    mpq_value out;
    root.export_mpq(m(), out);
    bool result = m().is_int_perfect_square(q.get(), out);
    root = rational(std::move(out));
    return result;
}

bool rational::is_perfect_square(rational& root) const {
    mpq_arg q(*this);
    mpq_value out;
    root.export_mpq(m(), out);
    bool result = m().is_perfect_square(q.get(), out);
    root = rational(std::move(out));
    return result;
}

bool rational::root(unsigned n, rational& root) const {
    mpq_arg q(*this);
    mpq_value out;
    root.export_mpq(m(), out);
    bool result = m().root(q.get(), n, out);
    root = rational(std::move(out));
    return result;
}

bool divides(rational const& a, rational const& b) {
    rational::mpq_arg av(a), bv(b);
    return rational::m().divides(av.get(), bv.get());
}

rational gcd(rational const& a, rational const& b) {
    SASSERT(a.is_int() && b.is_int());
    if (a.is_inline() && b.is_inline())
        return rational(std::gcd(a.small_num(), b.small_num()));
    rational::mpq_arg av(a), bv(b);
    rational::mpq_value out;
    rational::m().gcd(av.get(), bv.get(), out);
    return rational(std::move(out));
}

rational gcd(rational const& a, rational const& b, rational& x, rational& y) {
    rational::mpq_arg av(a), bv(b);
    rational::mpq_value out, xv, yv;
    rational::m().gcd(av.get(), bv.get(), xv, yv, out);
    rational result(std::move(out));
    x = rational(std::move(xv));
    y = rational(std::move(yv));
    return result;
}

rational lcm(rational const& a, rational const& b) {
    rational::mpq_arg av(a), bv(b);
    rational::mpq_value out;
    rational::m().lcm(av.get(), bv.get(), out);
    return rational(std::move(out));
}

rational bitwise_or(rational const& a, rational const& b) {
    rational::mpq_arg av(a), bv(b);
    rational::mpq_value out;
    rational::m().bitwise_or(av.get(), bv.get(), out);
    return rational(std::move(out));
}

rational bitwise_and(rational const& a, rational const& b) {
    rational::mpq_arg av(a), bv(b);
    rational::mpq_value out;
    rational::m().bitwise_and(av.get(), bv.get(), out);
    return rational(std::move(out));
}

rational bitwise_xor(rational const& a, rational const& b) {
    rational::mpq_arg av(a), bv(b);
    rational::mpq_value out;
    rational::m().bitwise_xor(av.get(), bv.get(), out);
    return rational(std::move(out));
}

rational bitwise_not(unsigned sz, rational const& a) {
    rational::mpq_arg av(a);
    rational::mpq_value out;
    rational::m().bitwise_not(sz, av.get(), out);
    return rational(std::move(out));
}

static void mk_power_up_to(vector<rational> & pws, unsigned n) {
    if (pws.empty()) {
        pws.push_back(rational::one());
    }
    unsigned sz = pws.size();
    rational curr = pws[sz - 1];
    rational two(2);
    for (unsigned i = sz; i <= n; ++i) {
        curr *= two;
        pws.push_back(curr);
    }
}

static DECLARE_MUTEX(g_powers_of_two);

rational rational::power_of_two(unsigned k) {
    rational result;
    {
        lock_guard lock(*g_powers_of_two);
        if (k >= m_powers_of_two.size())
            mk_power_up_to(m_powers_of_two, k+1);
        result = m_powers_of_two[k];
    }
    return result;
}

// in inf_rational.cpp
void initialize_inf_rational();
void finalize_inf_rational();

// in inf_int_rational.cpp
void initialize_inf_int_rational();
void finalize_inf_int_rational();

void rational::initialize() {
    if (!g_mpq_manager) {
        ALLOC_MUTEX(g_powers_of_two);
        g_mpq_manager = alloc(synch_mpq_manager);
        m_zero = 0;
        m_one = 1;
        m_minus_one = -1;
        initialize_inf_rational();
        initialize_inf_int_rational();
    }
}

void rational::finalize() {
    finalize_inf_rational();
    finalize_inf_int_rational();
    m_powers_of_two.finalize();
    m_zero.~rational();
    m_one.~rational();
    m_minus_one.~rational();
    dealloc(g_mpq_manager);
    g_mpq_manager = nullptr;
    DEALLOC_MUTEX(g_powers_of_two);
}

bool rational::limit_denominator(rational &num, rational const& limit) {
    rational n, d;
    n = numerator(num);
    d = denominator(num);
    if (d < limit) return false;
    
    /*
      Iteratively computes approximation using continuous fraction
      decomposition
      
      p(-1) = 0, p(0) = 1
      p(j) = t(j)*p(j-1) + p(j-2)
      
      q(-1) = 1, q(0) = 0
      q(j) = t(j)*q(j-1) + q(j-2)
      
      cf[t1; t2, ..., tr] =  p(r) / q(r) for r >= 1
      reference: https://www.math.u-bordeaux.fr/~pjaming/M1/exposes/MA2.pdf
    */
    
    rational p0(0), p1(1);
    rational q0(1), q1(0);
    
    while (!d.is_zero()) {
        rational tj(0), rem(0);
        rational p2(0), q2(0);
        tj = div(n, d);
        
        q2 = tj * q1 + q0;
        p2 = tj * p1 + p0;
        if (q2 >= limit) {
            num = p2/q2;
            return true;
        }
        rem = n - tj * d;
        p0 = p1;
        p1 = p2;
        q0 = q1;
        q1 = q2;
        n = d;
        d = rem;
    }
    return false;
}

bool rational::mult_inverse(unsigned num_bits, rational & result) const {
    rational const& n = *this;
    if (n.is_one()) {
        result = n;
        return true;
    }
    
    if (n.is_even())
        return false;
    
    rational g;
    rational x;
    rational y;
    g = gcd(n, rational::power_of_two(num_bits), x, y);
    if (x.is_neg()) {
        x = mod(x, rational::power_of_two(num_bits));
    }
    SASSERT(x.is_pos());
    SASSERT(mod(x * n, rational::power_of_two(num_bits)).is_one());
    result = x;
    return true;
}

/**
 * Compute the smallest multiplicative pseudo-inverse modulo 2^num_bits:
 *
 *      mod(n * n.pseudo_inverse(bits), 2^bits) == 2^k,
 *      where k is maximal such that 2^k divides n.
 *
 * Precondition: number is non-zero.
 */
rational rational::pseudo_inverse(unsigned num_bits) const {
    rational result;
    rational const& n = *this;
    SASSERT(!n.is_zero());  // TODO: or we define pseudo-inverse of 0 as 0.
    unsigned const k = n.trailing_zeros();
    rational const odd = machine_div2k(n, k);
    VERIFY(odd.mult_inverse(num_bits - k, result));
    SASSERT_EQ(mod(n * result, rational::power_of_two(num_bits)), rational::power_of_two(k));
    return result;
}
