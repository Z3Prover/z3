/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    rational.h

Abstract:

    Rational numbers

Author:

    Leonardo de Moura (leonardo) 2006-09-18.

--*/
#pragma once

#include <bit>
#include <numeric>
#include "util/mpq.h"
#include "util/memory_manager.h"

class rational {
    // Even words hold (signed numerator, 2 * denominator); odd words tag an owned mpq.
    uint64_t m_value = 2;
    // These bounds keep sums of cross products within signed 64-bit arithmetic.
    static constexpr int64_t inline_limit = (int64_t(1) << 30) - 1;
    static rational                  m_zero;
    static rational                  m_one;
    static rational                  m_minus_one;
    static vector<rational>          m_powers_of_two;
    static synch_mpq_manager*        g_mpq_manager;

    static synch_mpq_manager& m() { return *g_mpq_manager; }
    bool is_inline() const { return !(m_value & 1); }
    int32_t small_num() const { return std::bit_cast<int32_t>(uint32_t(m_value >> 32)); }
    uint32_t small_den() const { return uint32_t(m_value) >> 1; }
    mpq& large() const { return *reinterpret_cast<mpq*>(uintptr_t(m_value & ~uint64_t(1))); }
    static uint64_t encode(int32_t n, uint32_t d) {
        return (uint64_t(uint32_t(n)) << 32) | (uint64_t(d) << 1);
    }
    void release_large() noexcept;
    void release() noexcept {
        if (!is_inline()) release_large();
        m_value = 2;
    }
    void set_fraction(int64_t n, uint64_t d);
    void set(int64_t n, uint64_t d = 1) {
        if (d == 1 && -inline_limit <= n && n <= inline_limit) {
            release();
            m_value = encode(static_cast<int32_t>(n), 1);
        }
        else
            set_fraction(n, d);
    }
    void set(mpq&& q);
    void compact();
    unsigned large_hash() const;

    class mpq_arg {
        mpq m_small;
        mpq const* m_ref;
    public:
        explicit mpq_arg(rational const& r) : m_ref(r.is_inline() ? &m_small : &r.large()) {
            if (r.is_inline()) {
                if (r.small_den() == 1)
                    m().set(m_small, r.small_num());
                else
                    m().set(m_small, int64_t(r.small_num()), uint64_t(r.small_den()));
            }
        }
        ~mpq_arg() { synch_mpq_manager::del(g_mpq_manager, m_small); }
        mpq_arg(mpq_arg const&) = delete;
        mpq const& get() const { return *m_ref; }
    };

    enum class binary_op { add, sub, mul, div, rem };
    rational& apply(rational const& r, binary_op op);
    void display_hex(std::ostream& out, unsigned num_bits) const;
    void display_bin(std::ostream& out, unsigned num_bits) const;

public:
    // A conversion owns its limbs, including when bound to a const mpq&.
    class mpq_value : public mpq {
    public:
        mpq_value() = default;
        explicit mpq_value(mpz&& z) noexcept : mpq(std::move(z)) {}
        mpq_value(mpq_value&&) noexcept = default;
        mpq_value(mpq_value const&) = delete;
        ~mpq_value() { synch_mpq_manager::del(g_mpq_manager, *this); }
    };

    static void initialize();
    static void finalize();
    rational() noexcept = default;
    rational(rational const& r) : m_value(r.is_inline() ? r.m_value : 2) {
        if (!r.is_inline()) {
            mpq_value q;
            m().set(q, r.large());
            set(std::move(q));
        }
    }
    rational(rational&& r) noexcept : m_value(r.m_value) { r.m_value = 2; }
    explicit rational(int n) { set(n); }
    explicit rational(unsigned n) { set(n); }
    explicit rational(int64_t n) { set(n); }
    explicit rational(uint64_t n);
    rational(int n, int d) {
        SASSERT(d != 0);
        set(d < 0 ? -int64_t(n) : int64_t(n), d < 0 ? -int64_t(d) : int64_t(d));
    }
    rational(mpq const& q) { mpq_value v; m().set(v, q); set(std::move(v)); }
    rational(mpq&& q) { set(std::move(q)); }
    rational(mpz const& z) { mpq_value q; m().set(q, z); set(std::move(q)); }
    rational(mpz&& z) { mpq_value q(std::move(z)); set(std::move(q)); }
    explicit rational(double z) { UNREACHABLE(); }
    explicit rational(char const* v) { mpq_value q; m().set(q, v); set(std::move(q)); }
    explicit rational(unsigned const* v, unsigned sz) { mpq_value q; m().set(q, sz, v); set(std::move(q)); }
    struct i64 {};
    rational(int64_t i, i64) : rational(i) {}
    struct ui64 {};
    rational(uint64_t i, ui64) : rational(i) {}
    ~rational() { release(); }

    mpq_value to_mpq() const {
        mpq_value q;
        export_mpq(m(), q);
        return q;
    }
    template<bool SYNCH>
    void export_mpq(mpq_manager<SYNCH>& manager, mpq& q) const {
        if (is_inline()) {
            if (small_den() == 1)
                manager.set(q, small_num());
            else
                manager.set(q, int64_t(small_num()), uint64_t(small_den()));
        }
        else
            manager.set(q, large());
    }
    unsigned bitsize() const;
    unsigned storage_size() const { return is_inline() ? 2 : m().storage_size(large()); }
    void reset() { release(); }
    bool is_int() const { return is_inline() ? small_den() == 1 : m().is_int(large()); }
    bool is_small() const { return is_inline() || m().is_small(large()); }
    bool is_big() const { return !is_small(); }
    unsigned hash() const {
        if (!is_inline()) return large_hash();
        unsigned n = static_cast<unsigned>(small_num());
        return (small_num() < 0 ? 0u - n : n) + 3 * small_den();
    }
    struct hash_proc { unsigned operator()(rational const& r) const { return r.hash(); } };
    struct eq_proc { bool operator()(rational const& a, rational const& b) const { return a == b; } };
    void swap(rational& n) noexcept { std::swap(m_value, n.m_value); }
    std::string to_string() const;
    void display(std::ostream& out) const;
    void display_decimal(std::ostream& out, unsigned prec, bool truncate = false) const;
    void display_smt2(std::ostream& out) const;
    struct as_hex_wrapper { rational const& r; unsigned bw; };
    as_hex_wrapper as_hex(unsigned bw) const { return {*this, bw}; }
    friend std::ostream& operator<<(std::ostream& out, as_hex_wrapper const& r) {
        r.r.display_hex(out, r.bw); return out;
    }
    struct as_bin_wrapper { rational const& r; unsigned bw; };
    as_bin_wrapper as_bin(unsigned bw) const { return {*this, bw}; }
    friend std::ostream& operator<<(std::ostream& out, as_bin_wrapper const& r) {
        r.r.display_bin(out, r.bw); return out;
    }
    bool is_uint64() const { return is_inline() ? is_int() && small_num() >= 0 : m().is_uint64(large()); }
    bool is_int64() const { return is_inline() ? is_int() : m().is_int64(large()); }
    uint64_t get_uint64() const { SASSERT(is_uint64()); return is_inline() ? small_num() : m().get_uint64(large()); }
    int64_t get_int64() const { SASSERT(is_int64()); return is_inline() ? small_num() : m().get_int64(large()); }
    bool is_unsigned() const { return is_uint64() && get_uint64() < (1ull << 32); }
    unsigned get_unsigned() const { SASSERT(is_unsigned()); return static_cast<unsigned>(get_uint64()); }
    bool is_int32() const {
        if (!is_int64()) return false;
        int64_t v = get_int64();
        return INT_MIN <= v && v <= INT_MAX;
    }
    int get_int32() const { SASSERT(is_int32()); return static_cast<int>(get_int64()); }
    double get_double() const { return is_inline() ? double(small_num()) / small_den() : m().get_double(large()); }
    rational const& get_rational() const { return *this; }
    rational const& get_infinitesimal() const { return m_zero; }
    rational& operator=(rational&& r) noexcept {
        if (this != &r) { release(); m_value = r.m_value; r.m_value = 2; }
        return *this;
    }
    rational& operator=(rational const& r) {
        if (this != &r) { rational tmp(r); swap(tmp); }
        return *this;
    }
    rational& operator=(bool) = delete;
    rational operator*(bool) const = delete;
    rational& operator=(int v) { return *this = int64_t(v); }
    rational& operator=(int64_t v) { set(v); return *this; }
    rational& operator=(double) = delete;

    friend rational numerator(rational const& r) { return r.is_inline() ? rational(r.small_num()) : rational(r.large().numerator()); }
    friend rational denominator(rational const& r) { return r.is_inline() ? rational(r.small_den()) : rational(r.large().denominator()); }
    friend rational inv(rational const& r);
    rational& operator+=(rational const& r) {
        if (is_inline() && r.is_inline()) {
            if (small_den() == r.small_den())
                set(int64_t(small_num()) + r.small_num(), small_den());
            else
                set(int64_t(small_num()) * r.small_den() + int64_t(r.small_num()) * small_den(),
                    uint64_t(small_den()) * r.small_den());
            return *this;
        }
        return apply(r, binary_op::add);
    }
    rational& operator-=(rational const& r) {
        if (is_inline() && r.is_inline()) {
            if (small_den() == r.small_den())
                set(int64_t(small_num()) - r.small_num(), small_den());
            else
                set(int64_t(small_num()) * r.small_den() - int64_t(r.small_num()) * small_den(),
                    uint64_t(small_den()) * r.small_den());
            return *this;
        }
        return apply(r, binary_op::sub);
    }
    rational& operator*=(rational const& r) {
        if (is_inline() && r.is_inline()) {
            set(int64_t(small_num()) * r.small_num(), uint64_t(small_den()) * r.small_den());
            return *this;
        }
        return apply(r, binary_op::mul);
    }
    rational& operator/=(rational const& r) {
        if (is_inline() && r.is_inline() && !r.is_zero()) {
            int64_t n = int64_t(small_num()) * r.small_den();
            int64_t d = int64_t(small_den()) * r.small_num();
            set(d < 0 ? -n : n, d < 0 ? -d : d);
            return *this;
        }
        return apply(r, binary_op::div);
    }
    rational& operator%=(rational const& r) {
        if (is_inline() && r.is_inline() && is_int() && r.is_int() && !r.is_zero()) {
            set(small_num() % r.small_num());
            return *this;
        }
        return apply(r, binary_op::rem);
    }
    rational& operator+=(int v) { return *this += rational(v); }
    rational& operator-=(int v) { return *this -= rational(v); }
    rational& operator*=(int v) { return *this *= rational(v); }
    rational& operator/=(int v) { return *this /= rational(v); }
    rational& operator%=(int v) { return *this %= rational(v); }
    friend rational div(rational const& a, rational const& b);
    friend void div(rational const& a, rational const& b, rational& r) { r = div(a, b); }
    friend rational machine_div(rational const& a, rational const& b);
    friend rational machine_div_rem(rational const& a, rational const& b, rational& rem);
    friend rational machine_div2k(rational const& a, unsigned k);
    friend rational mod(rational const& a, rational const& b);
    friend void mod(rational const& a, rational const& b, rational& r) { r = mod(a, b); }
    friend rational mod2k(rational const& a, unsigned k);
    friend rational operator%(rational const& a, rational const& b) { return rational(a) %= b; }
    friend rational mod_hat(rational const& a, rational const& b);
    rational& operator++() { return *this += 1; }
    const rational operator++(int) { rational tmp(*this); ++*this; return tmp; }
    rational& operator--() { return *this -= 1; }
    const rational operator--(int) { rational tmp(*this); --*this; return tmp; }
    friend bool operator==(rational const& a, rational const& b) {
        if (a.m_value == b.m_value) return true;
        if (a.is_inline() && b.is_inline()) return false;
        mpq_arg av(a), bv(b);
        return m().eq(av.get(), bv.get());
    }
    friend bool operator<(rational const& a, rational const& b) {
        if (a.is_inline() && b.is_inline())
            return int64_t(a.small_num()) * b.small_den() < int64_t(b.small_num()) * a.small_den();
        mpq_arg av(a), bv(b);
        return m().lt(av.get(), bv.get());
    }
    void neg() {
        if (is_inline()) m_value = encode(-small_num(), small_den());
        else { m().neg(large()); compact(); }
    }
    bool is_zero() const { return is_inline() ? small_num() == 0 : m().is_zero(large()); }
    bool is_one() const { return m_value == encode(1, 1); }
    bool is_minus_one() const { return m_value == encode(-1, 1); }
    bool is_neg() const { return is_inline() ? small_num() < 0 : m().is_neg(large()); }
    bool is_pos() const { return is_inline() ? small_num() > 0 : m().is_pos(large()); }
    bool is_nonneg() const { return !is_neg(); }
    bool is_nonpos() const { return !is_pos(); }
    bool is_even() const { return is_inline() ? is_int() && !(small_num() & 1) : m().is_even(large()); }
    bool is_odd() const { return !is_even(); }
    friend rational floor(rational const& r);
    friend rational ceil(rational const& r);
    rational expt(int n) const;
    static rational power_of_two(unsigned k);
    bool is_power_of_two(unsigned& shift) const;
    bool is_power_of_two() const { unsigned shift; return is_power_of_two(shift); }
    bool mult_inverse(unsigned num_bits, rational& result) const;
    rational pseudo_inverse(unsigned num_bits) const;
    static rational const& zero() { return m_zero; }
    static rational const& one() { return m_one; }
    static rational const& minus_one() { return m_minus_one; }
    void addmul(rational const& c, rational const& k) {
        if (c.is_one()) *this += k;
        else if (c.is_minus_one()) *this -= k;
        else if (k.is_one()) *this += c;
        else if (k.is_minus_one()) *this -= c;
        else { rational tmp(k); tmp *= c; *this += tmp; }
    }
    void submul(rational const& c, rational const& k) {
        if (c.is_one()) *this -= k;
        else if (c.is_minus_one()) *this += k;
        else { rational tmp(k); tmp *= c; *this -= tmp; }
    }
    bool is_int_perfect_square(rational& root) const;
    bool is_perfect_square(rational& root) const;
    bool root(unsigned n, rational& root) const;
    friend std::ostream& operator<<(std::ostream& out, rational const& r) { return out << r.to_string(); }
    friend bool divides(rational const& a, rational const& b);
    friend rational gcd(rational const& a, rational const& b);
    friend rational gcd(rational const& a, rational const& b, rational& x, rational& y);
    friend rational lcm(rational const& a, rational const& b);
    friend rational bitwise_or(rational const& a, rational const& b);
    friend rational bitwise_and(rational const& a, rational const& b);
    friend rational bitwise_xor(rational const& a, rational const& b);
    friend rational bitwise_not(unsigned sz, rational const& a);
    friend rational abs(rational const& r) { rational result(r); if (result.is_neg()) result.neg(); return result; }
    rational to_rational() const { return *this; }
    static bool is_rational() { return true; }
    unsigned get_num_digits(rational const& base) const {
        SASSERT(is_int() && !is_neg());
        rational n = div(*this, base);
        unsigned digits = 1;
        while (n.is_pos()) { ++digits; n = div(n, base); }
        return digits;
    }
    unsigned get_num_bits() const { return get_num_digits(rational(2)); }
    unsigned get_num_decimal() const { return get_num_digits(rational(10)); }
    unsigned prev_power_of_two() const;
    unsigned next_power_of_two() const;
    bool get_bit(unsigned index) const;
    unsigned trailing_zeros() const {
        if (is_zero()) return 0;
        unsigned k = 0;
        for (; !get_bit(k); ++k) {}
        return k;
    }
    unsigned parity(unsigned num_bits) const;
    static bool limit_denominator(rational& num, rational const& limit);
};

static_assert(sizeof(rational) == 8);
Z3_ADD_INITIALIZER(rational, rational::initialize, 0);
Z3_ADD_FINALIZER(rational, rational::finalize);

inline bool operator!=(rational const & r1, rational const & r2) {
    return !operator==(r1, r2);
}

inline bool operator>(rational const & r1, rational const & r2) {
    return operator<(r2, r1);
}

inline bool operator<(int r1, rational const & r2) {
    return rational(r1) < r2;
}

inline bool operator<(rational const & r1, int r2) {
    return r1 < rational(r2);
}

inline bool operator<=(rational const & r1, rational const & r2) {
    return !operator>(r1, r2);
}

inline bool operator>=(rational const & r1, rational const & r2) {
    return !operator<(r1, r2);
}

inline bool operator>(rational const & a, int b) {
    return a > rational(b);
}

inline bool operator>(int a, rational const & b) {
    return rational(a) > b;
}

inline bool operator>=(rational const& a, int b) {
    return a >= rational(b);
}

inline bool operator>=(int a, rational const& b) {
    return rational(a) >= b;
}

inline bool operator<=(rational const& a, int b) {
    return a <= rational(b);
}

inline bool operator<=(int a, rational const& b) {
    return rational(a) <= b;
}

inline bool operator!=(rational const& a, int b) {
    return !(a == rational(b));
}

inline bool operator==(rational const & a, int b) {
    return a == rational(b);
}

inline rational operator+(rational const & r1, rational const & r2) {
    return rational(r1) += r2;
}

inline rational operator+(int r1, rational const & r2) {
    return rational(r1) + r2;
}

inline rational operator+(rational const & r1, int r2) {
    return r1 + rational(r2);
}

inline rational operator-(rational const & r1, rational const & r2) {
    return rational(r1) -= r2;
}

inline rational operator-(rational const & r1, int r2) {
    return r1 - rational(r2);
}

inline rational operator-(int r1, rational const & r2) {
    return rational(r1) - r2;
}

inline rational operator-(rational const & r) {
    rational result(r);
    result.neg();
    return result;
}

inline rational operator*(rational const & r1, rational const & r2) {
    return rational(r1) *= r2;
}

inline rational operator*(rational const & r1, bool r2) {
    UNREACHABLE();
    return r1 * rational(r2);
}

inline rational operator*(bool r1, rational const & r2) {
    UNREACHABLE();
    return rational(r1) * r2;
}

inline rational operator*(rational const & r1, int r2) {
    return r1 * rational(r2);
}

inline rational operator*(int r1, rational const & r2) {
    return rational(r1) * r2;
}

inline rational operator/(rational const & r1, rational const & r2) {
    return rational(r1) /= r2;
}

inline rational operator/(rational const & r1, int r2) {
    return r1 / rational(r2);
}

inline rational operator/(rational const & r1, bool r2) {
    UNREACHABLE();
    return r1 / rational(r2);
}

inline rational operator/(int r1, rational const & r2) {
    return rational(r1) / r2;
}

inline rational power(rational const & r, unsigned p) {
    return r.expt(p);
}

inline void swap(rational& r1, rational& r2) noexcept {
    r1.swap(r2);
}
inline rational mod_hat(rational const& a, rational const& b) {
    SASSERT(b.is_pos());
    rational r = mod(a, b);
    SASSERT(r.is_nonneg());
    if (b < r * 2) r -= b;
    return r;
}
inline unsigned rational::parity(unsigned num_bits) const {
    SASSERT(!is_neg() && *this < power_of_two(num_bits));
    return is_zero() ? num_bits : trailing_zeros();
}
