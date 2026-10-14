/*++
Copyright (c) 2026 Romain Soulat

Module Name:

    ff_field.h

Abstract:

    Fixed-width arithmetic for prime fields F_p.

    field64  : odd p < 2^63, Montgomery form on one 64-bit limb.
    field256 : odd p < 2^256, elements are stored in Montgomery form
               (a * 2^256 mod p) on four 64-bit limbs.

    Both expose the same interface so that the F4 backend (ff_f4.cpp) can be
    instantiated once per representation. Conversions to and from `rational`
    only happen at the boundary of the backend.

Author:

    Romain Soulat

--*/
#pragma once
#include "util/rational.h"
#include <cstdint>
#include <cstring>
#include <vector>

// Native MSVC does not provide a 128-bit integer type. Keep the ordinary
// engine and tiny-field search available there; F4 reports unsupported.
// The override also allows testing that fallback on a supporting compiler.
#ifndef Z3_FF_HAS_UINT128
# if defined(__SIZEOF_INT128__)
#  define Z3_FF_HAS_UINT128 1
# else
#  define Z3_FF_HAS_UINT128 0
# endif
#endif

#if Z3_FF_HAS_UINT128
#if defined(__GNUC__) || defined(__clang__)
#define FF_INLINE inline __attribute__((always_inline))
#else
#define FF_INLINE inline
#endif

namespace ff {

    // Bits of a non-negative rational, least significant first.
    inline void rational_bits(rational n, std::vector<bool> &bits) {
        bits.clear();
        rational two(2);
        while (n.is_pos()) {
            bits.push_back(!mod(n, two).is_zero());
            n = div(n, two);
        }
    }

    // Odd p < 2^63, elements in Montgomery form a * 2^64 mod p.
    class field64 {
    public:
        using elem = uint64_t;

    private:
        uint64_t m_p;
        uint64_t m_ninv;  // -p^{-1} mod 2^64
        uint64_t m_one;   // 2^64 mod p
        uint64_t m_r2;    // 2^128 mod p
        rational m_prime;

        uint64_t redc(unsigned __int128 t) const {
            uint64_t m = static_cast<uint64_t>(t) * m_ninv;
            unsigned __int128 u = (t + static_cast<unsigned __int128>(m) * m_p) >> 64;
            uint64_t r = static_cast<uint64_t>(u);
            return r >= m_p ? r - m_p : r;
        }

    public:
        explicit field64(rational const &p) : m_p(p.get_uint64()), m_prime(p) {
            uint64_t inv = m_p;
            for (unsigned i = 0; i < 6; ++i)
                inv *= 2 - m_p * inv;
            m_ninv = ~inv + 1;
            m_one = mod(rational::power_of_two(64), p).get_uint64();
            m_r2 = mod(rational::power_of_two(128), p).get_uint64();
        }
        static bool fits(rational const &p) {
            return p.is_uint64() && p.is_odd() && p < rational::power_of_two(63);
        }
        rational const &prime() const { return m_prime; }
        elem zero() const { return 0; }
        elem one() const { return m_one; }
        bool is_zero(elem a) const { return a == 0; }
        bool eq(elem a, elem b) const { return a == b; }
        elem add(elem a, elem b) const {
            uint64_t s = a + b;
            return s >= m_p ? s - m_p : s;
        }
        elem sub(elem a, elem b) const { return a >= b ? a - b : a + (m_p - b); }
        elem neg(elem a) const { return a ? m_p - a : 0; }
        elem mul(elem a, elem b) const { return redc(static_cast<unsigned __int128>(a) * b); }
        elem inv(elem a) const {
            // Invert the plain residue with extended Euclid, then return to Montgomery form.
            uint64_t plain = redc(a);
            __int128 t = 0, nt = 1, r = m_p, nr = plain;
            while (nr != 0) {
                __int128 q = r / nr, tmp;
                tmp = t - q * nt; t = nt; nt = tmp;
                tmp = r - q * nr; r = nr; nr = tmp;
            }
            if (t < 0)
                t += m_p;
            return mul(static_cast<uint64_t>(t), m_r2);
        }
        elem from_uint(uint64_t v) const { return mul(v % m_p, m_r2); }
        elem from(rational const &r) const { return from_uint(mod(r, m_prime).get_uint64()); }
        rational to(elem a) const { return rational(redc(a), rational::ui64()); }
        size_t hash(elem a) const { return static_cast<size_t>(a); }

        // Delayed reduction for p < 2^32: products of Montgomery residues are
        // below 2^64, so up to 2^64/p of them can be summed in 128 bits and
        // still satisfy the REDC precondition t < p*2^64.
        bool lazy_ok() const { return m_p < (uint64_t(1) << 32); }
        uint64_t lift(elem a) const { return a; }                 // multiplier for R mod p
        unsigned __int128 wide(elem a) const { return static_cast<unsigned __int128>(a) * m_one; }
        unsigned __int128 wide_mul(elem a, elem b) const { return static_cast<unsigned __int128>(a) * b; }
        elem reduce_wide(unsigned __int128 t) const { return redc(t); }
    };

    class field256 {
    public:
        struct elem {
            uint64_t w[4];
        };

    private:
        uint64_t m_p[4];
        uint64_t m_ninv;  // -p^{-1} mod 2^64
        bool m_nocarry;   // top limb small enough for the no-carry CIOS variant
        elem m_one;       // R mod p
        elem m_r2;        // R^2 mod p
        rational m_prime;

        static void limbs(rational v, uint64_t out[4]) {
            rational base = rational::power_of_two(64);
            for (unsigned i = 0; i < 4; ++i) {
                out[i] = mod(v, base).get_uint64();
                v = div(v, base);
            }
        }
        static rational value(uint64_t const w[4]) {
            rational r(0), base = rational::power_of_two(64);
            for (unsigned i = 4; i-- > 0;)
                r = r * base + rational(w[i], rational::ui64());
            return r;
        }
        FF_INLINE bool geq_p(uint64_t const a[4]) const {
            for (unsigned i = 4; i-- > 0;) {
                if (a[i] != m_p[i])
                    return a[i] > m_p[i];
            }
            return true;
        }
        FF_INLINE void sub_p(uint64_t a[4]) const {
            unsigned __int128 borrow = 0;
            for (unsigned i = 0; i < 4; ++i) {
                unsigned __int128 d = static_cast<unsigned __int128>(a[i]) - m_p[i] - borrow;
                a[i] = static_cast<uint64_t>(d);
                borrow = (d >> 64) ? 1 : 0;
            }
        }

    public:
        explicit field256(rational const &p) : m_prime(p) {
            limbs(p, m_p);
            // Newton iteration for p^{-1} mod 2^64 (p odd).
            uint64_t inv = m_p[0];
            for (unsigned i = 0; i < 6; ++i)
                inv *= 2 - m_p[0] * inv;
            m_ninv = ~inv + 1;
            m_nocarry = m_p[3] < 0x7ffffffffffffffeull;
            rational R = rational::power_of_two(256);
            limbs(mod(R, p), m_one.w);
            limbs(mod(R * R, p), m_r2.w);
        }
        static bool fits(rational const &p) {
            return p.is_pos() && p.is_odd() && p < rational::power_of_two(256);
        }
        rational const &prime() const { return m_prime; }
        elem zero() const { return elem{{0, 0, 0, 0}}; }
        elem one() const { return m_one; }
        bool is_zero(elem const &a) const { return (a.w[0] | a.w[1] | a.w[2] | a.w[3]) == 0; }
        bool eq(elem const &a, elem const &b) const { return std::memcmp(a.w, b.w, sizeof(a.w)) == 0; }

        FF_INLINE elem add(elem const &a, elem const &b) const {
            elem r;
            unsigned __int128 c = 0;
            for (unsigned i = 0; i < 4; ++i) {
                c += static_cast<unsigned __int128>(a.w[i]) + b.w[i];
                r.w[i] = static_cast<uint64_t>(c);
                c >>= 64;
            }
            if (c || geq_p(r.w))
                sub_p(r.w);
            return r;
        }
        elem sub(elem const &a, elem const &b) const {
            elem r;
            unsigned __int128 borrow = 0;
            for (unsigned i = 0; i < 4; ++i) {
                unsigned __int128 d = static_cast<unsigned __int128>(a.w[i]) - b.w[i] - borrow;
                r.w[i] = static_cast<uint64_t>(d);
                borrow = (d >> 64) ? 1 : 0;
            }
            if (borrow) {
                unsigned __int128 c = 0;
                for (unsigned i = 0; i < 4; ++i) {
                    c += static_cast<unsigned __int128>(r.w[i]) + m_p[i];
                    r.w[i] = static_cast<uint64_t>(c);
                    c >>= 64;
                }
            }
            return r;
        }
        elem neg(elem const &a) const { return sub(zero(), a); }

        // CIOS Montgomery multiplication: returns a*b*R^{-1} mod p.
        FF_INLINE elem mul(elem const &a, elem const &b) const {
            using u128 = unsigned __int128;
            if (m_nocarry) {
                // No-carry CIOS (valid when the top limb of p is < 2^63 - 1),
                // which covers the BN254 and BLS12-381 scalar fields.
                uint64_t t0 = 0, t1 = 0, t2 = 0, t3 = 0;
                for (unsigned i = 0; i < 4; ++i) {
                    uint64_t bi = b.w[i], A, C, m;
                    u128 v = static_cast<u128>(a.w[0]) * bi + t0;
                    t0 = static_cast<uint64_t>(v);
                    A = static_cast<uint64_t>(v >> 64);
                    m = t0 * m_ninv;
                    v = static_cast<u128>(m) * m_p[0] + t0;
                    C = static_cast<uint64_t>(v >> 64);
                    v = static_cast<u128>(a.w[1]) * bi + t1 + A;
                    t1 = static_cast<uint64_t>(v);
                    A = static_cast<uint64_t>(v >> 64);
                    v = static_cast<u128>(m) * m_p[1] + t1 + C;
                    t0 = static_cast<uint64_t>(v);
                    C = static_cast<uint64_t>(v >> 64);
                    v = static_cast<u128>(a.w[2]) * bi + t2 + A;
                    t2 = static_cast<uint64_t>(v);
                    A = static_cast<uint64_t>(v >> 64);
                    v = static_cast<u128>(m) * m_p[2] + t2 + C;
                    t1 = static_cast<uint64_t>(v);
                    C = static_cast<uint64_t>(v >> 64);
                    v = static_cast<u128>(a.w[3]) * bi + t3 + A;
                    t3 = static_cast<uint64_t>(v);
                    A = static_cast<uint64_t>(v >> 64);
                    v = static_cast<u128>(m) * m_p[3] + t3 + C;
                    t2 = static_cast<uint64_t>(v);
                    C = static_cast<uint64_t>(v >> 64);
                    t3 = C + A;
                }
                elem r{{t0, t1, t2, t3}};
                if (geq_p(r.w))
                    sub_p(r.w);
                return r;
            }
            uint64_t t[6] = {0, 0, 0, 0, 0, 0};
            for (unsigned i = 0; i < 4; ++i) {
                u128 c = 0;
                for (unsigned j = 0; j < 4; ++j) {
                    c += static_cast<u128>(a.w[j]) * b.w[i] + t[j];
                    t[j] = static_cast<uint64_t>(c);
                    c >>= 64;
                }
                c += t[4];
                t[4] = static_cast<uint64_t>(c);
                t[5] = static_cast<uint64_t>(c >> 64);
                uint64_t m = t[0] * m_ninv;
                c = static_cast<u128>(m) * m_p[0] + t[0];
                c >>= 64;
                for (unsigned j = 1; j < 4; ++j) {
                    c += static_cast<u128>(m) * m_p[j] + t[j];
                    t[j - 1] = static_cast<uint64_t>(c);
                    c >>= 64;
                }
                c += t[4];
                t[3] = static_cast<uint64_t>(c);
                t[4] = t[5] + static_cast<uint64_t>(c >> 64);
            }
            elem r{{t[0], t[1], t[2], t[3]}};
            if (t[4] || geq_p(r.w))
                sub_p(r.w);
            return r;
        }
        elem inv(elem const &a) const {
            // Fermat: a^{p-2}. Montgomery form is preserved by mul.
            uint64_t e[4];
            std::memcpy(e, m_p, sizeof(e));
            // p is odd and >= 3, so subtracting 2 never borrows past limb 0 unless p[0] < 2.
            unsigned __int128 d = static_cast<unsigned __int128>(e[0]) - 2;
            e[0] = static_cast<uint64_t>(d);
            for (unsigned i = 1; i < 4 && (d >> 64); ++i) {
                d = static_cast<unsigned __int128>(e[i]) - 1;
                e[i] = static_cast<uint64_t>(d);
            }
            elem r = m_one, base = a;
            for (unsigned i = 0; i < 4; ++i)
                for (unsigned b = 0; b < 64; ++b) {
                    if ((e[i] >> b) & 1)
                        r = mul(r, base);
                    base = mul(base, base);
                }
            return r;
        }
        elem from(rational const &r) const {
            elem x;
            limbs(mod(r, m_prime), x.w);
            return mul(x, m_r2);
        }
        elem from_uint(uint64_t v) const {
            elem x{{v, 0, 0, 0}};
            if (geq_p(x.w))
                return from(rational(v, rational::ui64()));
            return mul(x, m_r2);
        }
        rational to(elem const &a) const {
            elem plain{{1, 0, 0, 0}};
            elem x = mul(a, plain);
            return value(x.w);
        }
        size_t hash(elem const &a) const {
            return static_cast<size_t>(a.w[0] ^ (a.w[1] * 0x9e3779b97f4a7c15ull) ^ a.w[2] ^ a.w[3]);
        }
    };

}  // namespace ff

#endif // Z3_FF_HAS_UINT128
