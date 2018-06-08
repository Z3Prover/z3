/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    mpz.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2010-06-17.

Revision History:

--*/
#include<sstream>
#include "util/mpz.h"
#include "util/buffer.h"
#include "util/trace.h"
#include "util/hash.h"
#include "util/bit_util.h"

#if defined(_MP_INTERNAL)
#include "util/mpn.h"
#elif defined(_MP_GMP)
#include<gmp.h>
#else
#error No multi-precision library selected.
#endif

// Available GCD algorithms
// #define EUCLID_GCD
// #define BINARY_GCD
// #define LS_BINARY_GCD
// #define LEHMER_GCD

#if defined(_MP_GMP)
// Use LEHMER only if not using GMP
// LEHMER assumes 32-bit digits, so it cannot be used with MSBIGNUM library + 64-bit binary
#define EUCLID_GCD
#else
#define LEHMER_GCD
#endif


#include <immintrin.h> 

#if defined(__GNUC__)
#define _trailing_zeros32(X) __builtin_ctz(X)
#else
#define _trailing_zeros32(X) _tzcnt_u32(X)
#endif

#if defined(_AMD64_) 
 #if defined(__GNUC__)
 #define _trailing_zeros64(X) __builtin_ctzll(X)
 #else
 #define _trailing_zeros64(X) _tzcnt_u64(X)
 #endif
#else
inline uint64_t _trailing_zeros64(uint64_t x) {
    uint64_t r = 0;
    for (; 0 == (x & 1) && r < 64; ++r, x >>= 1);
    return r;
}
#endif


#define _bit_min(x, y) (y + ((x - y) & ((int)(x - y) >> 31)))
#define _bit_max(x, y) (x - ((x - y) & ((int)(x - y) >> 31)))


unsigned u_gcd(unsigned u, unsigned v) { 
    if (u == 0) return v;
    if (v == 0) return u;
    unsigned shift = _trailing_zeros32(u | v);
    u >>= _trailing_zeros32(u);
    if (u == 1 || v == 1) return 1 << shift; 
    if (u == v) return u << shift;
    do {
        v >>= _trailing_zeros32(v);        
#if 1
        unsigned diff = u - v;
        unsigned mdiff = diff & (unsigned)((int)diff >> 31);
        u = v + mdiff; // min
        v = diff - 2 * mdiff;   // if v <= u: u - v, if v > u: v - u = u - v - 2 * (u - v)
#endif
#if 0
        unsigned t = _bit_max(u, v);
        u = _bit_min(u, v);
        v = t;
        v -= u;        
#endif
#if 0
        unsigned t = std::max(u, v);
        u = std::min(u,v);
        v = t;
        v -= u;        
#endif
#if 0
        if (u > v) std::swap(u, v);
        v -= u;        
#endif
#if 0
        unsigned d1 = u - v;
        unsigned d2 = v - u;
        unsigned md21 = d2 & (unsigned)((int)d1 >> 31);
        unsigned md12 = d1 & (unsigned)((int)d2 >> 31);
        u = _bit_min(u, v);
        v = md12 | md21;
#endif
    }
    while (v != 0);
    return u << shift;
}

uint64_t u64_gcd(uint64_t u, uint64_t v) { 
    if (u == 0) return v;
    if (v == 0) return u;
    if (u == 1 || v == 1) return 1;
    auto shift = _trailing_zeros64(u | v);
    u >>= _trailing_zeros64(u);
    do {
        v >>= _trailing_zeros64(v);        
        if (u > v) std::swap(u, v);
        v -= u;        
    }
    while (v != 0);
    return u << shift;
}


template<bool SYNCH>
mpz_manager<SYNCH>::mpz_manager():
    m_allocator("mpz_manager") {
    if (SYNCH)
        omp_init_nest_lock(&m_lock);
#ifndef _MP_GMP
    if (sizeof(digit_t) == sizeof(uint64_t)) {
        // 64-bit machine
        m_init_cell_capacity = 4;
    }
    else {
        m_init_cell_capacity = 6;
    }
    for (unsigned i = 0; i < 2; i++) {
        m_tmp[i] = allocate(m_init_cell_capacity);
        m_arg[i] = allocate(m_init_cell_capacity);
        m_arg[i]->m_size = 1;
    }
    set(m_int_min, -static_cast<int64_t>(INT_MIN));
#else
    // GMP
    mpz_init(m_tmp);
    mpz_init(m_tmp2);
    mpz_init(m_two32);
    mpz_set_ui(m_two32, UINT_MAX);
    mpz_set_ui(m_tmp, 1);
    mpz_add(m_two32, m_two32, m_tmp);
    m_arg[0] = allocate();
    m_arg[1] = allocate();
    mpz_init(m_uint64_max);
    unsigned max_l = static_cast<unsigned>(UINT64_MAX);
    unsigned max_h = static_cast<unsigned>(UINT64_MAX >> 32);
    mpz_set_ui(m_uint64_max, max_h);
    mpz_mul(m_uint64_max, m_two32, m_uint64_max);
    mpz_set_ui(m_tmp, max_l);
    mpz_add(m_uint64_max, m_uint64_max, m_tmp);
    mpz_init(m_int64_max);
    mpz_init(m_int64_min);

    max_l = static_cast<unsigned>(INT64_MAX % static_cast<int64_t>(UINT_MAX));
    max_h = static_cast<unsigned>(INT64_MAX / static_cast<int64_t>(UINT_MAX));
    mpz_set_ui(m_int64_max, max_h);
    mpz_set_ui(m_tmp, UINT_MAX);
    mpz_mul(m_int64_max, m_tmp, m_int64_max);
    mpz_set_ui(m_tmp, max_l);
    mpz_add(m_int64_max, m_tmp, m_int64_max);
    mpz_neg(m_int64_min, m_int64_max);
    mpz_sub_ui(m_int64_min, m_int64_min, 1);
#endif
    
    mpz one(1);
    set(m_two64, (uint64_t)UINT64_MAX);
    add(m_two64, one, m_two64);
}

template<bool SYNCH>
mpz_manager<SYNCH>::~mpz_manager() {
    del(m_two64);
#ifndef _MP_GMP
    del(m_int_min);
    for (unsigned i = 0; i < 2; i++) {
        deallocate(m_tmp[i]);
        deallocate(m_arg[i]);
    }
#else
    mpz_clear(m_tmp);
    mpz_clear(m_tmp2);
    mpz_clear(m_two32);
    deallocate(m_arg[0]);
    deallocate(m_arg[1]);
    mpz_clear(m_uint64_max);
    mpz_clear(m_int64_max);
    mpz_clear(m_int64_min);
#endif
    if (SYNCH)
        omp_destroy_nest_lock(&m_lock);
}

template<bool SYNCH>
void mpz_manager<SYNCH>::set_big_i64(mpz & c, int64_t v) {
#ifndef _MP_GMP
    if (is_small(c)) {
        c.m_ptr = allocate(m_init_cell_capacity);
    }
    SASSERT(capacity(c) >= m_init_cell_capacity);
    uint64_t _v;
    if (v < 0) {
        _v = -v;
        c.m_val = -1;
    }
    else {
        _v = v;
        c.m_val = 1;
    }
    if (sizeof(digit_t) == sizeof(uint64_t)) {
        // 64-bit machine
        digits(c)[0] = static_cast<digit_t>(_v);
        c.m_ptr->m_size = 1;
    }
    else {
        // 32-bit machine
        digits(c)[0] = static_cast<unsigned>(_v);
        digits(c)[1] = static_cast<unsigned>(_v >> 32);
        c.m_ptr->m_size = digits(c)[1] == 0 ? 1 : 2;
    }
#else
    if (is_small(c)) {
        c.m_ptr = allocate();
    }
    uint64_t _v;
    bool sign;
    if (v < 0) {
        _v   = -v;
        sign = true;
    }
    else {
        _v   = v;
        sign = false;
    }
    mpz_set_ui(*c.m_ptr, static_cast<unsigned>(_v));
    mpz_set_ui(m_tmp,    static_cast<unsigned>(_v >> 32));
    mpz_mul(m_tmp, m_tmp, m_two32);
    mpz_add(*c.m_ptr, *c.m_ptr, m_tmp);
    if (sign)
        mpz_neg(*c.m_ptr, *c.m_ptr);
#endif
}

template<bool SYNCH>
void mpz_manager<SYNCH>::set_big_ui64(mpz & c, uint64_t v) {
#ifndef _MP_GMP
    if (is_small(c)) {
        c.m_ptr = allocate(m_init_cell_capacity);
    }
    SASSERT(capacity(c) >= m_init_cell_capacity);
    c.m_val = 1;
    if (sizeof(digit_t) == sizeof(uint64_t)) {
        // 64-bit machine
        digits(c)[0] = static_cast<digit_t>(v);
        c.m_ptr->m_size = 1;
    }
    else {
        // 32-bit machine
        digits(c)[0] = static_cast<unsigned>(v);
        digits(c)[1] = static_cast<unsigned>(v >> 32);
        c.m_ptr->m_size = digits(c)[1] == 0 ? 1 : 2;
    }
#else
    if (is_small(c)) {
        c.m_ptr = allocate();
    }
    mpz_set_ui(*c.m_ptr, static_cast<unsigned>(v));
    mpz_set_ui(m_tmp,    static_cast<unsigned>(v >> 32));
    mpz_mul(m_tmp, m_tmp, m_two32);
    mpz_add(*c.m_ptr, *c.m_ptr, m_tmp);
#endif
}

#ifndef _MP_GMP
template<bool SYNCH>
template<int IDX>
void mpz_manager<SYNCH>::set(mpz & a, int sign, unsigned sz) {
#if 0
    static unsigned max_sz = 0;
    if (sz > max_sz) {
        max_sz = sz;
        verbose_stream() << "max_sz: " << max_sz << "\n";
    }
#endif
    unsigned i = sz;
    for (; i > 0; --i) {
        if (m_tmp[IDX]->m_digits[i-1] != 0)
            break;
    }

    if (i == 0) {
        // m_tmp[IDX] is zero
        reset(a);
        return;
    }
    
    if (i == 1 && m_tmp[IDX]->m_digits[0] <= INT_MAX) {
        // m_tmp[IDX] fits is a fixnum
        del(a);
        a.m_val = sign < 0 ? -static_cast<int>(m_tmp[IDX]->m_digits[0]) : static_cast<int>(m_tmp[IDX]->m_digits[0]);
        return;
    }

    a.m_val = sign;
    std::swap(a.m_ptr, m_tmp[IDX]);
    a.m_ptr->m_size = i;
    if (!m_tmp[IDX]) // 'a' was a small number
        m_tmp[IDX] = allocate(m_init_cell_capacity);
}
#endif

template<bool SYNCH>
void mpz_manager<SYNCH>::set(mpz & a, char const * val) {
    reset(a);
    mpz ten(10);
    mpz tmp;
    char const * str = val;
    bool sign = false;
    while (str[0] == ' ') ++str;
    if (str[0] == '-') 
        sign = true;
    while (str[0]) {
        if ('0' <= str[0] && str[0] <= '9') {
            SASSERT(str[0] - '0' <= 9);
            mul(a, ten, tmp);
            add(tmp, mk_z(str[0] - '0'), a); 
        }
        ++str;
    }
    del(tmp);
    if (sign)
        neg(a);
}

template<bool SYNCH>
void mpz_manager<SYNCH>::set(mpz & target, unsigned sz, digit_t const * digits) {
    // remove zero digits
    while (sz > 0 && digits[sz - 1] == 0)
        sz--;
    if (sz == 0)
        reset(target);
    else if (sz == 1)
        set(target, digits[0]);
    else {
#ifndef _MP_GMP
        target.m_val = 1; // number is positive.
        if (is_small(target)) {
            unsigned c = sz < m_init_cell_capacity ? m_init_cell_capacity : sz;
            target.m_ptr             = allocate(c);
            target.m_ptr->m_size     = sz;
            target.m_ptr->m_capacity = c;
            memcpy(target.m_ptr->m_digits, digits, sizeof(digit_t) * sz);
        }
        else {
            if (capacity(target) < sz) {
                SASSERT(sz > m_init_cell_capacity);
                deallocate(target.m_ptr);
                target.m_ptr = allocate(sz);
                target.m_ptr->m_size     = sz;
                target.m_ptr->m_capacity = sz;
                memcpy(target.m_ptr->m_digits, digits, sizeof(digit_t) * sz);
            }
            else {
                target.m_ptr->m_size = sz;
                memcpy(target.m_ptr->m_digits, digits, sizeof(digit_t) * sz);
            }
        }
#else
    mk_big(target);
    // reset
    mpz_set_ui(*target.m_ptr, digits[sz - 1]);
    SASSERT(sz > 0);
    unsigned i = sz - 1;
    while (i > 0) {
      --i;
      mpz_mul_2exp(*target.m_ptr, *target.m_ptr, 32);
      mpz_set_ui(m_tmp, digits[i]);
      mpz_add(*target.m_ptr, *target.m_ptr, m_tmp);
    }
#endif        
    }
}

#ifndef _MP_GMP
template<bool SYNCH>
template<bool SUB>
void mpz_manager<SYNCH>::big_add_sub(mpz const & a, mpz const & b, mpz & c) {
    int sign_a;
    int sign_b;
    mpz_cell * cell_a;
    mpz_cell * cell_b;
    get_sign_cell<0>(a, sign_a, cell_a);
    get_sign_cell<1>(b, sign_b, cell_b);
    if (SUB)
        sign_b = -sign_b;
    size_t real_sz;
    if (sign_a == sign_b) {
        unsigned sz  = std::max(cell_a->m_size, cell_b->m_size)+1;
        ensure_tmp_capacity<0>(sz);
        m_mpn_manager.add(cell_a->m_digits, cell_a->m_size,
                          cell_b->m_digits, cell_b->m_size, 
                          m_tmp[0]->m_digits, sz, &real_sz);
        SASSERT(real_sz <= sz);
        set<0>(c, sign_a, static_cast<unsigned>(real_sz));
    }
    else {
        digit_t borrow;
        int r = m_mpn_manager.compare(cell_a->m_digits, cell_a->m_size,
                                      cell_b->m_digits, cell_b->m_size);
        if (r == 0) {
            reset(c);
        }
        else if (r < 0) {
            // a < b
            unsigned sz = cell_b->m_size;
            ensure_tmp_capacity<0>(sz);
            m_mpn_manager.sub(cell_b->m_digits,
                              cell_b->m_size,
                              cell_a->m_digits,
                              cell_a->m_size,
                              m_tmp[0]->m_digits,
                              &borrow);
            SASSERT(borrow == 0);
            set<0>(c, sign_b, sz);
        }
        else {
            // a > b
            unsigned sz = cell_a->m_size;
            ensure_tmp_capacity<0>(sz);
            m_mpn_manager.sub(cell_a->m_digits,
                              cell_a->m_size,
                              cell_b->m_digits,
                              cell_b->m_size,
                              m_tmp[0]->m_digits,
                              &borrow);
            SASSERT(borrow == 0);
            set<0>(c, sign_a, sz);
        }
    }
}
#endif

template<bool SYNCH>
void mpz_manager<SYNCH>::big_add(mpz const & a, mpz const & b, mpz & c) {
#ifndef _MP_GMP
    big_add_sub<false>(a, b, c);
#else
    // GMP version
    mpz_t * arg0;
    mpz_t * arg1;
    get_arg<0>(a, arg0);
    get_arg<1>(b, arg1);
    mk_big(c);
    mpz_add(*c.m_ptr, *arg0, *arg1);
#endif
}

template<bool SYNCH>
void mpz_manager<SYNCH>::big_sub(mpz const & a, mpz const & b, mpz & c) {
#ifndef _MP_GMP
    big_add_sub<true>(a, b, c);
#else
    // GMP version
    mpz_t * arg0;
    mpz_t * arg1;
    get_arg<0>(a, arg0);
    get_arg<1>(b, arg1);
    mk_big(c);
    mpz_sub(*c.m_ptr, *arg0, *arg1);
#endif
}

template<bool SYNCH>
void mpz_manager<SYNCH>::big_mul(mpz const & a, mpz const & b, mpz & c) {
#ifndef _MP_GMP
    int sign_a;
    int sign_b;
    mpz_cell * cell_a;
    mpz_cell * cell_b;
    get_sign_cell<0>(a, sign_a, cell_a);
    get_sign_cell<1>(b, sign_b, cell_b);
    unsigned sz  = cell_a->m_size + cell_b->m_size;
    ensure_tmp_capacity<0>(sz);
    m_mpn_manager.mul(cell_a->m_digits,
                      cell_a->m_size,
                      cell_b->m_digits,
                      cell_b->m_size,
                      m_tmp[0]->m_digits);
    set<0>(c, sign_a == sign_b ? 1 : -1, sz);
#else
    // GMP version
    mpz_t * arg0;
    mpz_t * arg1;
    get_arg<0>(a, arg0);
    get_arg<1>(b, arg1);
    mk_big(c);
    mpz_mul(*c.m_ptr, *arg0, *arg1);
#endif
}

#ifndef _MP_GMP
template<bool SYNCH>
template<qr_mode MODE>
void mpz_manager<SYNCH>::quot_rem_core(mpz const & a, mpz const & b, mpz & q, mpz & r) {
    /*
      +26 / +7 = +3, remainder is +5
      -26 / +7 = -3, remainder is -5
      +26 / -7 = -3, remainder is +5
      -26 / -7 = +3, remainder is -5 
    */
    int sign_a;
    int sign_b;
    mpz_cell * cell_a;
    mpz_cell * cell_b;
    get_sign_cell<0>(a, sign_a, cell_a);
    get_sign_cell<1>(b, sign_b, cell_b);
    if (cell_b->m_size > cell_a->m_size) {
        if (MODE == REM_ONLY || MODE == QUOT_AND_REM)
            set(r, a); 
        if (MODE == QUOT_ONLY || MODE == QUOT_AND_REM)
            reset(q);
        return;
    }
    unsigned q_sz = cell_a->m_size - cell_b->m_size + 1;
    unsigned r_sz = cell_b->m_size;
    ensure_tmp_capacity<0>(q_sz);
    ensure_tmp_capacity<1>(r_sz);
    m_mpn_manager.div(cell_a->m_digits, cell_a->m_size,
                      cell_b->m_digits, cell_b->m_size,                      
                       m_tmp[0]->m_digits,
                       m_tmp[1]->m_digits);
    if (MODE == QUOT_ONLY || MODE == QUOT_AND_REM)
        set<0>(q, sign_a == sign_b ? 1 : -1, q_sz);
    if (MODE == REM_ONLY || MODE == QUOT_AND_REM)
        set<1>(r, sign_a, r_sz);
}
#endif

template<bool SYNCH>
void mpz_manager<SYNCH>::big_div_rem(mpz const & a, mpz const & b, mpz & q, mpz & r) {
#ifndef _MP_GMP
    quot_rem_core<QUOT_AND_REM>(a, b, q, r);
#else
    // GMP version
    mpz_t * arg0;
    mpz_t * arg1;
    get_arg<0>(a, arg0);
    get_arg<1>(b, arg1);
    mk_big(q);
    mk_big(r);
    mpz_tdiv_qr(*q.m_ptr, *r.m_ptr, *arg0, *arg1);
#endif
}

template<bool SYNCH>
void mpz_manager<SYNCH>::big_div(mpz const & a, mpz const & b, mpz & c) {
#ifndef _MP_GMP
    mpz dummy;
    quot_rem_core<QUOT_ONLY>(a, b, c, dummy);
    SASSERT(is_zero(dummy));
#else
    // GMP version
    mpz_t * arg0;
    mpz_t * arg1;
    get_arg<0>(a, arg0);
    get_arg<1>(b, arg1);
    mk_big(c);
    mpz_tdiv_q(*c.m_ptr, *arg0, *arg1);
#endif
} 

template<bool SYNCH>
void mpz_manager<SYNCH>::big_rem(mpz const & a, mpz const & b, mpz & c) {
#ifndef _MP_GMP
    mpz dummy;
    quot_rem_core<REM_ONLY>(a, b, dummy, c);
    SASSERT(is_zero(dummy));
#else
    // GMP version
    mpz_t * arg0;
    mpz_t * arg1;
    get_arg<0>(a, arg0);
    get_arg<1>(b, arg1);
    mk_big(c);
    mpz_tdiv_r(*c.m_ptr, *arg0, *arg1);
#endif
}

template<bool SYNCH>
void mpz_manager<SYNCH>::gcd(mpz const & a, mpz const & b, mpz & c) {
    static_assert(sizeof(a.m_val) == sizeof(int), "size mismatch");
    if (is_small(a) && is_small(b) && a.m_val != INT_MIN && b.m_val != INT_MIN) {
        int _a = a.m_val;
        int _b = b.m_val;
        if (_a < 0) _a = -_a;
        if (_b < 0) _b = -_b;
        unsigned r = u_gcd(_a, _b);
        set(c, r);
    }
    else {
#ifdef _MP_GMP
        mpz_t * arg0;
        mpz_t * arg1;
        get_arg<0>(a, arg0);
        get_arg<1>(b, arg1);
        mk_big(c);
        mpz_gcd(*c.m_ptr, *arg0, *arg1);
        return;
#endif
        if (is_zero(a)) {
            set(c, b);
            abs(c);
            return;
        }
        if (is_zero(b)) {
            set(c, a);
            abs(c);
            return;
        }
#ifdef BINARY_GCD
        // Binary GCD for big numbers
        // - It doesn't use division
        // - The initial experiments, don't show any performance improvement
        // - It only works with _MP_INTERNAL
        mpz u, v, diff;
        set(u, a);
        set(v, b);
        abs(u);
        abs(v);

        unsigned k_u = power_of_two_multiple(u);
        unsigned k_v = power_of_two_multiple(v);
        unsigned k   = k_u < k_v ? k_u : k_v;

        machine_div2k(u, k_u);

        while (true) {
            machine_div2k(v, k_v);
 
            if (lt(u, v)) {
                sub(v, u, v);
            } 
            else {
                sub(u, v, diff);
                swap(u, v);
                swap(v, diff);
            }
            
            if (is_zero(v) || is_one(v))
                break;
            
            // reset least significant bit
            if (is_small(v))
                v.m_val &= ~1;
            else
                v.m_ptr->m_digits[0] &= ~static_cast<digit_t>(1);
            k_v = power_of_two_multiple(v);
        }

        mul2k(u, k, c);
        del(u); del(v); del(diff);
#endif // BINARY_GCD

#ifdef EUCLID_GCD
        mpz tmp1;
        mpz tmp2;
        mpz aux;
        set(tmp1, a);
        set(tmp2, b);
        abs(tmp1);
        abs(tmp2);
        if (lt(tmp1, tmp2))
            swap(tmp1, tmp2);
        if (is_zero(tmp2)) {
            swap(c, tmp1);
        }
        else {
            while (true) {
                if (is_uint64(tmp1) && is_uint64(tmp2)) {
                    set(c, u64_gcd(get_uint64(tmp1), get_uint64(tmp2)));
                    break;
                }
                rem(tmp1, tmp2, aux);
                if (is_zero(aux)) {
                    swap(c, tmp2);
                    break;
                }
                swap(tmp1, tmp2);
                swap(tmp2, aux);
            }
        }
        del(tmp1); del(tmp2); del(aux);
#endif // EUCLID_GCD

#ifdef LS_BINARY_GCD
        mpz u, v, t, u1, u2;
        set(u, a);
        set(v, b);
        abs(u);
        abs(v);
        if (lt(u, v))
            swap(u, v);
        while (!is_zero(v)) {
            // Basic idea:
            // compute t = 2^e*v  such that t <= u < 2t
            // u := min{u - t, 2t - u}
            // 
            // The assignment u := min{u - t, 2t - u}
            // can be replaced with u := u - t
            // 
            // Since u and v are positive, we have:
            //    2^{log2(u)}     <= u < 2^{(log2(u) + 1)}
            //    2^{log2(v)}     <= v < 2^{(log2(v) + 1)}
            //  -->
            //    2^{log2(v)}*2^{log2(u)-log2(v)} <= v*2^{log2(u)-log2(v)} < 2^{log2(v) + 1}*2^{log2(u)-log2(v)}
            //  -->
            //    2^{log2(u)} <= v*2^{log2(u)-log2(v)} < 2^{log2(u) + 1}
            //  
            // Now, let t be v*2^{log2(u)-log2(v)}
            // If t <= u, then we found t
            // Otherwise t = t div 2
            unsigned k_u = log2(u);
            unsigned k_v = log2(v);
            SASSERT(k_v <= k_u);
            unsigned e   = k_u - k_v;
            mul2k(v, e, t);
            sub(u, t, u1);
            if (is_neg(u1)) {
                // t is too big
                machine_div2k(t, 1);
                // Now, u1 contains u - 2t
                neg(u1); 
                // Now, u1 contains 2t - u
                sub(u, t, u2); // u2 := u - t
            }
            else {
                // u1 contains u - t
                mul2k(t, 1);
                sub(t, u, u2);
                // u2 contains 2t - u
            }
            SASSERT(is_nonneg(u1));
            SASSERT(is_nonneg(u2));
            if (lt(u1, u2))
                swap(u, u1);
            else
                swap(u, u2);
            if (lt(u, v))
                swap(u,v);
        }
        swap(u, c);
        del(u); del(v); del(t); del(u1); del(u2);
#endif // LS_BINARY_GCD

#ifdef LEHMER_GCD
        // For now, it only works if sizeof(digit_t) == sizeof(unsigned)
        static_assert(sizeof(digit_t) == sizeof(unsigned), "");
        
        int64_t a_hat, b_hat, A, B, C, D, T, q, a_sz, b_sz;
        mpz a1, b1, t, r, tmp;
        set(a1, a);
        set(b1, b);
        abs(a1);
        abs(b1);
        if (lt(a1, b1))
            swap(a1, b1);
        while (true) {
            SASSERT(ge(a1, b1));
            if (is_small(b1)) {
                if (is_small(a1)) {
                    unsigned r = u_gcd(a1.m_val, b1.m_val);
                    set(c, r);
                    break;
                }
                else {
                    while (!is_zero(b1)) {
                        SASSERT(ge(a1, b1));
                        rem(a1, b1, tmp);
                        swap(a1, b1);
                        swap(b1, tmp);
                    }
                    swap(c, a1);
                    break;
                }
            }
            SASSERT(!is_small(a1));
            SASSERT(!is_small(b1));
            a_sz  = a1.m_ptr->m_size;
            b_sz  = b1.m_ptr->m_size;
            SASSERT(b_sz <= a_sz);
            a_hat = a1.m_ptr->m_digits[a_sz - 1];
            b_hat = (b_sz == a_sz) ? b1.m_ptr->m_digits[b_sz - 1] : 0;
            A = 1; 
            B = 0;
            C = 0;
            D = 1;
            while (true) {
                // Loop invariants
                SASSERT(a_hat + A <= static_cast<int64_t>(UINT_MAX) + 1);
                SASSERT(a_hat + B <  static_cast<int64_t>(UINT_MAX) + 1);
                SASSERT(b_hat + C <  static_cast<int64_t>(UINT_MAX) + 1);
                SASSERT(b_hat + D <= static_cast<int64_t>(UINT_MAX) + 1);
                // overflows can't happen since I'm using int64
                if (b_hat + C == 0 || b_hat + D == 0)
                    break;
                q  = (a_hat + A)/(b_hat + C);
                if (q != (a_hat + B)/(b_hat + D))
                    break;
                T = A - q*C;
                A = C;
                C = T;
                T = B - q*D;
                B = D;
                D = T;
                T = a_hat - q*b_hat;
                a_hat = b_hat;
                b_hat = T;
            }
            SASSERT(ge(a1, b1));
            if (B == 0) {
                rem(a1, b1, t);
                swap(a1, b1);
                swap(b1, t);
                SASSERT(ge(a1, b1));
            }
            else {
                // t <- A*a1
                set(tmp, A);
                mul(a1, tmp, t); 
                // t <- t + B*b1
                set(tmp, B);
                addmul(t, tmp, b1, t);
                // r <- C*a1
                set(tmp, C);
                mul(a1, tmp, r);
                // r <- r + D*b1
                set(tmp, D);
                addmul(r, tmp, b1, r);
                // a <- t
                swap(a1, t);
                // b <- r
                swap(b1, r);
                SASSERT(ge(a1, b1));
            }
        }
        del(a1); del(b1); del(r); del(t); del(tmp);
#endif // LEHMER_GCD
    }
}

template<bool SYNCH>
unsigned mpz_manager<SYNCH>::size_info(mpz const & a) {
    if (is_small(a))
        return 1;
#ifndef _MP_GMP
    return a.m_ptr->m_size + 1;
#else
    return mpz_size(*a.m_ptr);
#endif
}

template<bool SYNCH>
struct mpz_manager<SYNCH>::sz_lt {
    mpz_manager<SYNCH> & m;
    mpz const *          m_as;
    
    sz_lt(mpz_manager<SYNCH> & _m, mpz const * as):m(_m), m_as(as) {}

    bool operator()(unsigned p1, unsigned p2) {
        return m.size_info(m_as[p1]) < m.size_info(m_as[p2]);
    }
};

template<bool SYNCH>
void mpz_manager<SYNCH>::gcd(unsigned sz, mpz const * as, mpz & g) {
#if 0
    // Optimization: sort numbers by size. Motivation: compute the gcd of the small ones first.
    // The optimization did not really help.
    switch (sz) {
    case 0:
        reset(g);
        return;
    case 1:
        set(g, as[0]);
        abs(g);
        return;
    case 2:
        gcd(as[0], as[1], g);
        return;
    default:
        break;
    }
    unsigned i;
    for (i = 0; i < sz; i++) {
        if (!is_small(as[i]))
            break;
    }
    if (i != sz) {
        // array has big numbers
        sbuffer<unsigned, 1024> p;
        for (i = 0; i < sz; i++)
            p.push_back(i);
        sz_lt lt(*this, as);
        std::sort(p.begin(), p.end(), lt);
        TRACE("mpz_gcd", for (unsigned i = 0; i < sz; i++) tout << p[i] << ":" << size_info(as[p[i]]) << " "; tout << "\n";);
        gcd(as[p[0]], as[p[1]], g);
        for (i = 2; i < sz; i++) {
            if (is_one(g))
                return;
            gcd(g, as[p[i]], g);
        }
        return;
    }
    else {
        gcd(as[0], as[1], g);
        for (unsigned i = 2; i < sz; i++) {
            if (is_one(g))
                return;
            gcd(g, as[i], g);
        }
    }
#else
    // Vanilla implementation
    switch (sz) {
    case 0:
        reset(g);
        return;
    case 1:
        set(g, as[0]);
        abs(g);
        return;
    default:
        break;
    }
    gcd(as[0], as[1], g);
    for (unsigned i = 2; i < sz; i++) {
        if (is_one(g))
            return;
        gcd(g, as[i], g);
    }
#endif
}

template<bool SYNCH>
void mpz_manager<SYNCH>::gcd(mpz const & r1, mpz const & r2, mpz & a, mpz & b, mpz & r) {
    mpz tmp1, tmp2;
    mpz aux, quot;
    set(tmp1, r1);
    set(tmp2, r2);
    set(a, 1);
    set(b, 0);
    mpz nexta, nextb;
    set(nexta, 0);
    set(nextb, 1);

    abs(tmp1);
    abs(tmp2);
    if (lt(tmp1, tmp2)) {
        swap(tmp1, tmp2);
        swap(nexta, nextb);
        swap(a, b);
    }

    // tmp1 >= tmp2 >= 0
    // quot_rem in one function would be faster.
    while (is_pos(tmp2)) {
        SASSERT(ge(tmp1, tmp2));

        // aux = tmp2
        set(aux, tmp2);
        // quot = div(tmp1, tmp2);
        machine_div(tmp1, tmp2, quot);
        // tmp2 = tmp1 % tmp2
        rem(tmp1, tmp2, tmp2);
        // tmp1 = aux
        set(tmp1, aux);
        // aux = nexta
        set(aux, nexta);
        // nexta = a - (quot*nexta)
        mul(quot, nexta, nexta);
        sub(a, nexta, nexta);
        // a = axu
        set(a, aux);
        // aux = nextb
        set(aux, nextb);
        // nextb = b - (quot*nextb)
        mul(nextb, quot, nextb);
        sub(b, nextb, nextb);
        // b = aux
        set(b, aux);
    }

    if (is_neg(r1))
        neg(a);
    if (is_neg(r2))
        neg(b);

    // SASSERT((a*r1) + (b*r2) == tmp1);
#ifdef Z3DEBUG
    mul(a, r1, nexta);
    mul(b, r2, nextb);
    add(nexta, nextb, nexta);
    SASSERT(eq(nexta, tmp1));
#endif
    set(r, tmp1);
    del(tmp1);
    del(tmp2);
    del(aux);
    del(quot);
    del(nexta);
    del(nextb);
}

template<bool SYNCH>
void mpz_manager<SYNCH>::lcm(mpz const & a, mpz const & b, mpz & c) {
    if (is_one(b)) {
        set(c, a);
        TRACE("lcm_bug", tout << "1. lcm(" << to_string(a) << ", " << to_string(b) << ") = " << to_string(c) << "\n";);
    }
    else if (is_one(a) || eq(a, b)) {
        set(c, b);
        TRACE("lcm_bug", tout << "2. lcm(" << to_string(a) << ", " << to_string(b) << ") = " << to_string(c) << "\n";);
    }
    else {
        mpz r;
        gcd(a, b, r);
        TRACE("lcm_bug", tout << "gcd(" << to_string(a) << ", " << to_string(b) << ") = " << to_string(r) << "\n";);
        if (eq(r, a)) {
            set(c, b);
            TRACE("lcm_bug", tout << "3. lcm(" << to_string(a) << ", " << to_string(b) << ") = " << to_string(c) << "\n";);
        }
        else if (eq(r, b)) {
            set(c, a);
            TRACE("lcm_bug", tout << "4. lcm(" << to_string(a) << ", " << to_string(b) << ") = " << to_string(c) << "\n";);
        }
        else {
            // c contains gcd(a, b)   
            // so c divides a, and machine_div(a, c) is equal to div(a, c)
            machine_div(a, r, r);
            mul(r, b, c);
            TRACE("lcm_bug", tout << "5. lcm(" << to_string(a) << ", " << to_string(b) << ") = " << to_string(c) << "\n";);
        }
        del(r);
    }
}

template<bool SYNCH>
void mpz_manager<SYNCH>::bitwise_or(mpz const & a, mpz const & b, mpz & c) {
    SASSERT(is_nonneg(a));
    SASSERT(is_nonneg(b));
    TRACE("mpz", tout << "is_small(a): " << is_small(a) << ", is_small(b): " << is_small(b) << "\n";);
    if (is_small(a) && is_small(b)) {
        del(c);
        c.m_val = a.m_val | b.m_val;
    }
    else {
#ifndef _MP_GMP
        mpz a1, b1, a2, b2, m, tmp;
        set(a1, a);
        set(b1, b);
        set(m, 1);
        reset(c);
        while (!is_zero(a1) && !is_zero(b1)) {
            TRACE("mpz", tout << "a1: " << to_string(a1) << ", b1: " << to_string(b1) << "\n";);
            mod(a1, m_two64, a2);
            mod(b1, m_two64, b2);
            TRACE("mpz", tout << "a2: " << to_string(a2) << ", b2: " << to_string(b2) << "\n";);
            uint64_t v = get_uint64(a2) | get_uint64(b2);
            TRACE("mpz", tout << "uint(a2): " << get_uint64(a2) << ", uint(b2): " << get_uint64(b2) << "\n";);
            set(tmp, v);
            mul(tmp, m, tmp);
            add(c, tmp, c); // c += m * v
            mul(m, m_two64, m);
            div(a1, m_two64, a1);
            div(b1, m_two64, b1);
        }
        if (!is_zero(a1)) {
            mul(a1, m, a1);
            add(c, a1, c);
        }
        if (!is_zero(b1)) {
            mul(b1, m, b1);
            add(c, b1, c);
        }
        del(a1); del(b1); del(a2); del(b2); del(m); del(tmp);
#else
        mpz_t * arg0;
        mpz_t * arg1;
        get_arg<0>(a, arg0);
        get_arg<1>(b, arg1);
        mk_big(c);
        mpz_ior(*c.m_ptr, *arg0, *arg1);
#endif
    }
}

template<bool SYNCH>
void mpz_manager<SYNCH>::bitwise_and(mpz const & a, mpz const & b, mpz & c) {
    SASSERT(is_nonneg(a));
    SASSERT(is_nonneg(b));
    if (is_small(a) && is_small(b)) {
        del(c);
        c.m_val = a.m_val & b.m_val;
    }
    else {
#ifndef _MP_GMP
        mpz a1, b1, a2, b2, m, tmp;
        set(a1, a);
        set(b1, b);
        set(m, 1);
        reset(c);
        while (!is_zero(a1) && !is_zero(b1)) {
            mod(a1, m_two64, a2);
            mod(b1, m_two64, b2);
            uint64_t v = get_uint64(a2) & get_uint64(b2);
            set(tmp, v);
            mul(tmp, m, tmp);
            add(c, tmp, c); // c += m * v
            mul(m, m_two64, m);
            div(a1, m_two64, a1);
            div(b1, m_two64, b1);
        }
        del(a1); del(b1); del(a2); del(b2); del(m); del(tmp);
#else
        mpz_t * arg0;
        mpz_t * arg1;
        get_arg<0>(a, arg0);
        get_arg<1>(b, arg1);
        mk_big(c);
        mpz_and(*c.m_ptr, *arg0, *arg1);
#endif
    }
}

template<bool SYNCH>
void mpz_manager<SYNCH>::bitwise_xor(mpz const & a, mpz const & b, mpz & c) {
    SASSERT(is_nonneg(a));
    SASSERT(is_nonneg(b));
    if (is_small(a) && is_small(b)) {
        set_i64(c, i64(a) ^ i64(b));
    }
    else {
#ifndef _MP_GMP
        mpz a1, b1, a2, b2, m, tmp;
        set(a1, a);
        set(b1, b);
        set(m, 1);
        reset(c);
        while (!is_zero(a1) && !is_zero(b1)) {
            mod(a1, m_two64, a2);
            mod(b1, m_two64, b2);
            uint64_t v = get_uint64(a2) ^ get_uint64(b2);
            set(tmp, v);
            mul(tmp, m, tmp);
            add(c, tmp, c); // c += m * v
            mul(m, m_two64, m);
            div(a1, m_two64, a1);
            div(b1, m_two64, b1);
        }
        if (!is_zero(a1)) {
            mul(a1, m, a1);
            add(c, a1, c);
        }
        if (!is_zero(b1)) {
            mul(b1, m, b1);
            add(c, b1, c);
        }
        del(a1); del(b1); del(a2); del(b2); del(m); del(tmp);
#else
        mpz_t * arg0;
        mpz_t * arg1;
        get_arg<0>(a, arg0);
        get_arg<1>(b, arg1);
        mk_big(c);
        mpz_xor(*c.m_ptr, *arg0, *arg1);
#endif
    }
}

template<bool SYNCH>
void mpz_manager<SYNCH>::bitwise_not(unsigned sz, mpz const & a, mpz & c) {
    SASSERT(is_nonneg(a));
    if (is_small(a) && sz <= 63) {
        int64_t mask = (static_cast<int64_t>(1) << sz) - static_cast<int64_t>(1);
        set_i64(c, (~ i64(a)) & mask);
    }
    else {
        mpz a1, a2, m, tmp;
        set(a1, a);
        set(m, 1);
        set(c, 0);
        while (sz > 0) {
            mod(a1, m_two64, a2);
            uint64_t n = get_uint64(a2);
            uint64_t v = ~n;
            SASSERT(~v == n);
            if (sz < 64) {
                uint64_t mask = (1ull << static_cast<uint64_t>(sz)) - 1ull;
                v = mask & v;
            }
            TRACE("bitwise_not", tout << "sz: " << sz << ", v: " << v << ", n: " << n << "\n";);
            set(tmp, v);
            SASSERT(get_uint64(tmp) == v);
            mul(tmp, m, tmp);
            add(c, tmp, c); // c += m * v
            mul(m, m_two64, m);
            div(a1, m_two64, a1);
            sz -= (sz<64) ? sz : 64; 
        }
        del(a1); del(a2); del(m); del(tmp);
        TRACE("bitwise_not", tout << "sz: " << sz << " a: " << to_string(a) << " c: " << to_string(c) << "\n";);
    }
}

template<bool SYNCH>
void mpz_manager<SYNCH>::big_set(mpz & target, mpz const & source) {
#ifndef _MP_GMP
    if (&target == &source)
        return;
    target.m_val = source.m_val;
    if (is_small(target)) {
        target.m_ptr = allocate(capacity(source));
        target.m_ptr->m_size     = size(source);
        target.m_ptr->m_capacity = capacity(source);
        memcpy(target.m_ptr->m_digits, source.m_ptr->m_digits, sizeof(digit_t) * size(source));
    }
    else {
        if (capacity(target) < size(source)) {
            deallocate(target.m_ptr);
            target.m_ptr = allocate(capacity(source));
            target.m_ptr->m_size     = size(source);
            target.m_ptr->m_capacity = capacity(source);
            memcpy(target.m_ptr->m_digits, source.m_ptr->m_digits, sizeof(digit_t) * size(source));
        }
        else {
            target.m_ptr->m_size = size(source);
            memcpy(target.m_ptr->m_digits, source.m_ptr->m_digits, sizeof(digit_t) * size(source));
        }
    }
#else
    // GMP version
    mk_big(target);
    mpz_set(*target.m_ptr, *source.m_ptr);
#endif
}

template<bool SYNCH>
int mpz_manager<SYNCH>::big_compare(mpz const & a, mpz const & b) {
#ifndef _MP_GMP
    int sign_a;
    int sign_b;
    mpz_cell * cell_a;
    mpz_cell * cell_b;
    get_sign_cell<0>(a, sign_a, cell_a);
    get_sign_cell<1>(b, sign_b, cell_b);

    if (sign_a > 0) {
        // a is positive
        if (sign_b > 0) {
            // a & b are positive
            return m_mpn_manager.compare(cell_a->m_digits, cell_a->m_size,
                                         cell_b->m_digits, cell_b->m_size);
        }
        else {
            // b is negative
            return 1; // a > b
        }
    }
    else {
        // a is negative
        if (sign_b > 0) {
            // b is positive
            return -1; // a < b
        }
        else {
            // a & b are negative
            return m_mpn_manager.compare(cell_b->m_digits, cell_b->m_size,
                                         cell_a->m_digits, cell_a->m_size);
        }
    }
#else
    // GMP version
    mpz_t * arg0;
    mpz_t * arg1;
    get_arg<0>(a, arg0);
    get_arg<1>(b, arg1);
    return mpz_cmp(*arg0, *arg1);
#endif
}

template<bool SYNCH>
bool mpz_manager<SYNCH>::is_uint64(mpz const & a) const {
#ifndef _MP_GMP
    if (a.m_val < 0)
        return false;
    if (is_small(a))
        return true;
    if (sizeof(digit_t) == sizeof(uint64_t)) {
        return size(a) <= 1;
    }
    else {
        return size(a) <= 2;
    }
#else
    // GMP version
    if (is_small(a))
        return a.m_val >= 0;
    return is_nonneg(a) && mpz_cmp(*a.m_ptr, m_uint64_max) <= 0;
#endif
}

template<bool SYNCH>
bool mpz_manager<SYNCH>::is_int64(mpz const & a) const {
    if (is_small(a))
        return true;
#ifndef _MP_GMP
    if (!is_abs_uint64(a)) 
        return false;
    uint64_t num = big_abs_to_uint64(a);
    uint64_t msb = static_cast<uint64_t>(1) << 63;
    uint64_t msb_val = msb & num;
    if (a.m_val >= 0) {
        // non-negative number.
        return (0 == msb_val);
    }
    else {
        // negative number.
        // either the high bit is 0, or
        // the number is 2^64 which can be represented.
        //
        return 0 == msb_val || (msb_val == num);
    }
#else
    // GMP version
    return mpz_cmp(m_int64_min, *a.m_ptr) <= 0 && mpz_cmp(*a.m_ptr, m_int64_max) <= 0;
#endif
}

template<bool SYNCH>
uint64_t mpz_manager<SYNCH>::get_uint64(mpz const & a) const {
    if (is_small(a)) 
        return static_cast<uint64_t>(a.m_val);
#ifndef _MP_GMP
    SASSERT(a.m_ptr->m_size > 0);
    return big_abs_to_uint64(a);
#else
    // GMP version
    if (sizeof(uint64_t) == sizeof(unsigned long)) {
        return mpz_get_ui(*a.m_ptr);
    }
    else {
        mpz_manager * _this = const_cast<mpz_manager*>(this);
        mpz_set(_this->m_tmp, *a.m_ptr);
        mpz_mod(_this->m_tmp, m_tmp, m_two32);
        uint64_t r = static_cast<uint64_t>(mpz_get_ui(m_tmp));
        mpz_set(_this->m_tmp, *a.m_ptr);
        mpz_div(_this->m_tmp, m_tmp, m_two32);
        r += static_cast<uint64_t>(mpz_get_ui(m_tmp)) << static_cast<uint64_t>(32);
        return r;
    }
#endif
}

template<bool SYNCH>
int64_t mpz_manager<SYNCH>::get_int64(mpz const & a) const {
    if (is_small(a))
        return static_cast<int64_t>(a.m_val);
#ifndef _MP_GMP
    SASSERT(is_int64(a));
    uint64_t num = big_abs_to_uint64(a);
    if (a.m_val < 0) {
        if (num != 0 && (num << 1) == 0)
            return INT64_MIN;
        return -static_cast<int64_t>(num);
    }
    return static_cast<int64_t>(num);
#else
    // GMP
    if (sizeof(int64_t) == sizeof(long) || mpz_fits_slong_p(*a.m_ptr)) {
        return mpz_get_si(*a.m_ptr);
    }
    else {
        mpz_manager * _this = const_cast<mpz_manager*>(this);
        mpz_mod(_this->m_tmp, *a.m_ptr, m_two32);
        int64_t r = static_cast<int64_t>(mpz_get_ui(m_tmp));
        mpz_div(_this->m_tmp, *a.m_ptr, m_two32);
        r += static_cast<int64_t>(mpz_get_si(m_tmp)) << static_cast<int64_t>(32);
        return r;
    }
#endif
}

template<bool SYNCH>
double mpz_manager<SYNCH>::get_double(mpz const & a) const {
    if (is_small(a))
        return static_cast<double>(a.m_val);
#ifndef _MP_GMP
    double r = 0.0;
    double d = 1.0;
    unsigned sz = size(a);
    for (unsigned i = 0; i < sz; i++) {
        r += d * static_cast<double>(digits(a)[i]);
        if (sizeof(digit_t) == sizeof(uint64_t))
            d *= static_cast<double>(UINT64_MAX); // 64-bit version
        else
            d *= static_cast<double>(UINT_MAX);   // 32-bit version
    }
    return a.m_val < 0 ? -r : r;
#else
    return mpz_get_d(*a.m_ptr);
#endif
}

template<bool SYNCH>
void mpz_manager<SYNCH>::display(std::ostream & out, mpz const & a) const {
    if (is_small(a)) {
        out << a.m_val;
    }
    else {
#ifndef _MP_GMP
        if (a.m_val < 0)
            out << "-";
        if (sizeof(digit_t) == 4) {
            sbuffer<char, 1024> buffer(11*size(a), 0);
            out << m_mpn_manager.to_string(digits(a), size(a), buffer.begin(), buffer.size());
        }
        else {
            sbuffer<char, 1024> buffer(21*size(a), 0);
            out << m_mpn_manager.to_string(digits(a), size(a), buffer.begin(), buffer.size());
        }
#else
        // GMP version
        size_t sz = mpz_sizeinbase(*a.m_ptr, 10) + 2;
        sbuffer<char, 1024> buffer(sz, 0);
        mpz_get_str(buffer.c_ptr(), 10, *a.m_ptr);
        out << buffer.c_ptr();
#endif
    } 
}

template<bool SYNCH>
void mpz_manager<SYNCH>::display_smt2(std::ostream & out, mpz const & a, bool decimal) const {
    if (is_neg(a)) {
        mpz_manager<SYNCH> * _this = const_cast<mpz_manager<SYNCH>*>(this);
        _scoped_numeral<mpz_manager<SYNCH> > tmp(*_this);
        _this->set(tmp, a);
        _this->neg(tmp);
        out << "(- ";
        display(out, tmp);
        if (decimal)
            out << ".0";
        out << ")";
    }
    else {
        display(out, a);
        if (decimal)
            out << ".0";
    }
}

template<bool SYNCH>
std::string mpz_manager<SYNCH>::to_string(mpz const & a) const {
    std::ostringstream buffer;
    display(buffer, a);
    return buffer.str();
}

template<bool SYNCH>
unsigned mpz_manager<SYNCH>::hash(mpz const & a) {
    if (is_small(a))
        return a.m_val;
#ifndef _MP_GMP
    unsigned sz = size(a);
    if (sz == 1)
        return static_cast<unsigned>(digits(a)[0]);
    return string_hash(reinterpret_cast<char*>(digits(a)), sz * sizeof(digit_t), 17);
#else
    return mpz_get_si(*a.m_ptr);
#endif
}

template<bool SYNCH>
void mpz_manager<SYNCH>::power(mpz const & a, unsigned p, mpz & b) {
#ifdef _MP_GMP
    if (!is_small(a)) {
        mk_big(b);
        mpz_pow_ui(*b.m_ptr, *a.m_ptr, p);
        return;
    }
#endif
#ifndef _MP_GMP
    if (is_small(a)) {
        if (a.m_val == 2) {
            if (p < 8 * sizeof(int) - 1) {
                del(b);
                b.m_val = 1 << p;
            }
            else {
                unsigned sz    = p/(8 * sizeof(digit_t)) + 1;
                unsigned shift = p%(8 * sizeof(digit_t));
                SASSERT(sz > 0);
                allocate_if_needed(b, sz);
                SASSERT(b.m_ptr->m_capacity >= sz);
                b.m_ptr->m_size     = sz;
                for (unsigned i = 0; i < sz - 1; i++)
                    b.m_ptr->m_digits[i] = 0;
                b.m_ptr->m_digits[sz-1] = 1 << shift;
                b.m_val = 1;
            }
            return;
        }
        if (a.m_val == 0) {
            SASSERT(p != 0);
            reset(b);
            return;
        }
        if (a.m_val == 1) {
            set(b, 1);
            return;
        }
    }
#endif
    // general purpose
    unsigned mask = 1;
    mpz power;
    set(power, a);
    set(b, 1);
    while (mask <= p) {
        if (mask & p)
            mul(b, power, b);
        mul(power, power, power);
        mask = mask << 1;
    }
    del(power);
}

template<bool SYNCH>
bool mpz_manager<SYNCH>::is_power_of_two(mpz const & a) {
    unsigned shift;
    return is_power_of_two(a, shift);
}

template<bool SYNCH>
bool mpz_manager<SYNCH>::is_power_of_two(mpz const & a, unsigned & shift) {
    if (is_nonpos(a))
        return false;
    if (is_small(a)) {
        if (::is_power_of_two(a.m_val)) {
            shift = ::log2((unsigned)a.m_val);
            return true;
        }
        else {
            return false;
        }
    }
#ifndef _MP_GMP
    mpz_cell * c     = a.m_ptr;
    unsigned sz      = c->m_size;
    digit_t * ds     = c->m_digits;
    for (unsigned i = 0; i < sz - 1; i++) {
        if (ds[i] != 0)
            return false;
    }
    digit_t v = ds[sz-1];
    if (!(v & (v - 1)) && v) {
        shift = log2(a);
        return true;
    }
    else {
        return false;
    }
#else
    if (mpz_popcount(*a.m_ptr) == 1) {
        shift = log2(a);
        return true;
    }
    else {
        return false;
    }
#endif
}

// Expand capacity of a
#ifndef _MP_GMP
template<bool SYNCH>
void mpz_manager<SYNCH>::ensure_capacity(mpz & a, unsigned capacity) {
    if (capacity <= 1)
        return;
    if (capacity < m_init_cell_capacity)
        capacity = m_init_cell_capacity;
    if (is_small(a)) {
        a.m_ptr = allocate(capacity);
        SASSERT(a.m_ptr->m_capacity == capacity);
        if (a.m_val == INT_MIN) {
            unsigned intmin_sz = m_int_min.m_ptr->m_size;
            for (unsigned i = 0; i < intmin_sz; i++)
                a.m_ptr->m_digits[i] = m_int_min.m_ptr->m_digits[i];
            a.m_val = -1;
            a.m_ptr->m_size = m_int_min.m_ptr->m_size;
        }
        else if (a.m_val < 0) {
            a.m_ptr->m_digits[0] = -a.m_val;
            a.m_val = -1;
            a.m_ptr->m_size = 1;
        }
        else {
            a.m_ptr->m_digits[0] =  a.m_val;
            a.m_val = 1;
            a.m_ptr->m_size = 1;
        }
    }
    else {
        if (a.m_ptr->m_capacity >= capacity)
            return;
        mpz_cell * new_cell = allocate(capacity);
        SASSERT(new_cell->m_capacity == capacity);
        unsigned old_sz  = a.m_ptr->m_size;
        new_cell->m_size = old_sz;
        for (unsigned i = 0; i < old_sz; i++)
            new_cell->m_digits[i] = a.m_ptr->m_digits[i];
        deallocate(a.m_ptr);
        a.m_ptr = new_cell;
    }
}

template<bool SYNCH>
void mpz_manager<SYNCH>::normalize(mpz & a) {
    mpz_cell * c = a.m_ptr;
    digit_t * ds = c->m_digits;
    unsigned i = c->m_size;
    for (; i > 0; --i) {
        if (ds[i-1] != 0)
            break;
    }

    if (i == 0) {
        // a is zero...
        reset(a);
        return;
    }
    
    if (i == 1 && ds[0] <= INT_MAX) {
        // a is small
        int val = a.m_val < 0 ? -static_cast<int>(ds[0]) : static_cast<int>(ds[0]);
        del(a);
        a.m_val = val;
        return;
    }
    // adjust size
    c->m_size = i;
}
#endif

template<bool SYNCH>
void mpz_manager<SYNCH>::machine_div2k(mpz & a, unsigned k) {
    if (k == 0 || is_zero(a))
        return;
    if (is_small(a)) {
        if (k < 32) {
            int twok = 1 << k;
            a.m_val /= twok;
        }
        else {
            a.m_val = 0;
        }
        return;
    }
#ifndef _MP_GMP
    unsigned digit_shift = k / (8 * sizeof(digit_t));
    mpz_cell * c         = a.m_ptr;
    unsigned sz          = c->m_size;
    if (digit_shift >= sz) {
        reset(a);
        return;
    }
    unsigned bit_shift   = k % (8 * sizeof(digit_t));
    unsigned comp_shift  = (8 * sizeof(digit_t)) - bit_shift;
    unsigned new_sz      = sz - digit_shift;
    SASSERT(new_sz >= 1);
    digit_t * ds = c->m_digits;
    TRACE("mpz_2k", tout << "bit_shift: " << bit_shift << ", comp_shift: " << comp_shift << ", new_sz: " << new_sz << ", sz: " << sz << "\n";);
    if (new_sz < sz) {
        unsigned i       = 0;
        unsigned j       = digit_shift;
        if (bit_shift != 0) {
            for (; i < new_sz - 1; i++, j++) {
                ds[i] = ds[j];
                ds[i] >>= bit_shift;
                ds[i] |= (ds[j+1] << comp_shift);
            }
            ds[i] = ds[j];
            ds[i] >>= bit_shift;
        }
        else {
            for (; i < new_sz; i++, j++) {
                ds[i] = ds[j];
            }
        }
    }
    else {
        SASSERT(new_sz == sz);
        SASSERT(bit_shift != 0);
        unsigned i       = 0;
        for (; i < new_sz - 1; i++) {
            ds[i] >>= bit_shift;
            ds[i] |= (ds[i+1] << comp_shift);
        }
        ds[i] >>= bit_shift;
    }
    
    c->m_size = new_sz;
    normalize(a);
#else
    MPZ_BEGIN_CRITICAL();
    mpz_t * arg0;
    get_arg<0>(a, arg0);
    mpz_tdiv_q_2exp(m_tmp, *arg0, k);
    mk_big(a);
    mpz_swap(*a.m_ptr, m_tmp);
    MPZ_END_CRITICAL();
#endif    
}

template<bool SYNCH>
void mpz_manager<SYNCH>::mul2k(mpz & a, unsigned k) {
    if (k == 0 || is_zero(a))
        return;
    if (is_small(a) && k < 32) {
        set_i64(a, i64(a) * (static_cast<int64_t>(1) << k));
        return;
    }
#ifndef _MP_GMP
    TRACE("mpz_mul2k", tout << "mul2k\na: " << to_string(a) << "\nk: " << k << "\n";);
    unsigned word_shift  = k / (8 * sizeof(digit_t));
    unsigned bit_shift   = k % (8 * sizeof(digit_t));
    unsigned old_sz      = is_small(a) ? 1 : a.m_ptr->m_size;
    unsigned new_sz      = old_sz + word_shift + 1;
    ensure_capacity(a, new_sz);
    TRACE("mpz_mul2k", tout << "word_shift: " << word_shift << "\nbit_shift: " << bit_shift << "\nold_sz: " << old_sz << "\nnew_sz: " << new_sz 
          << "\na after ensure capacity:\n" << to_string(a) << "\n";);
    SASSERT(!is_small(a));
    mpz_cell * cell_a    = a.m_ptr;
    old_sz = cell_a->m_size;
    digit_t * ds         = cell_a->m_digits;
    for (unsigned i = old_sz; i < new_sz; i++) 
        ds[i] = 0;
    cell_a->m_size       = new_sz;

    if (word_shift > 0) {
        unsigned j = old_sz;
        unsigned i = old_sz + word_shift;
        while (j > 0) {
            --j; --i;
            ds[i] = ds[j];
        }
        while (i > 0) {
            --i;
            ds[i] = 0;
        }
    }
    if (bit_shift > 0) {
        DEBUG_CODE({
            for (unsigned i = 0; i < word_shift; i++) {
                SASSERT(ds[i] == 0);
            }
        });
        unsigned comp_shift = (8 * sizeof(digit_t)) - bit_shift;
        digit_t prev = 0;
        for (unsigned i = word_shift; i < new_sz; i++) {
            digit_t new_prev = (ds[i] >> comp_shift);
            ds[i] <<= bit_shift;
            ds[i] |= prev;
            prev = new_prev;
        }
    }
    normalize(a);
    TRACE("mpz_mul2k", tout << "mul2k result:\n" << to_string(a) << "\n";);
#else
    mpz_t * arg0;
    get_arg<0>(a, arg0);
    mk_big(a);
    mpz_mul_2exp(*a.m_ptr, *arg0, k);
#endif
}

#ifndef _MP_GMP
static_assert(sizeof(digit_t) == 4 || sizeof(digit_t) == 8, "");
#endif

template<bool SYNCH>
unsigned mpz_manager<SYNCH>::power_of_two_multiple(mpz const & a) {
    if (is_zero(a))
        return 0;
    if (is_small(a)) {
        unsigned r = 0;
        int v      = a.m_val;
#define COUNT_DIGIT_RIGHT_ZEROS()               \
        if (v % (1 << 16) == 0) {               \
            r += 16;                            \
            v /= (1 << 16);                     \
        }                                       \
        if (v % (1 << 8) == 0) {                \
            r += 8;                             \
            v /= (1 << 8);                      \
        }                                       \
        if (v % (1 << 4) == 0) {                \
            r += 4;                             \
            v /= (1 << 4);                      \
        }                                       \
        if (v % (1 << 2) == 0) {                \
            r += 2;                             \
            v /= (1 << 2);                      \
        }                                       \
        if (v % 2 == 0) {                       \
            r++;                                \
        }
        COUNT_DIGIT_RIGHT_ZEROS();
        return r;
    }
#ifndef _MP_GMP
    mpz_cell * c        = a.m_ptr;
    unsigned sz         = c->m_size;
    unsigned r          = 0;
    digit_t * source    = c->m_digits; 
    for (unsigned i = 0; i < sz; i++) {
        if (source[i] != 0) {
            digit_t v = source[i];
            if (sizeof(digit_t) == 8) {
                // TODO: we can remove this if after we move to MPN
                // In MPN the digit_t is always an unsigned integer
                if (static_cast<uint64_t>(v) % (static_cast<uint64_t>(1) << 32) == 0) {
                    r += 32;                     
                    v = static_cast<digit_t>(static_cast<uint64_t>(v) / (static_cast<uint64_t>(1) << 32));
                }                                
            }
            COUNT_DIGIT_RIGHT_ZEROS();
            return r;
        }
        r += (8 * sizeof(digit_t));
    }
    return r;
#else
    return mpz_scan1(*a.m_ptr, 0);
#endif
}

template<bool SYNCH>
unsigned mpz_manager<SYNCH>::log2(mpz const & a) {
    if (is_nonpos(a))
        return 0;
    if (is_small(a))
        return ::log2((unsigned)a.m_val);
#ifndef _MP_GMP
    static_assert(sizeof(digit_t) == 8 || sizeof(digit_t) == 4, "");
    mpz_cell * c     = a.m_ptr;
    unsigned sz      = c->m_size;
    digit_t * ds     = c->m_digits; 
    if (sizeof(digit_t) == 8) 
        return (sz - 1)*64 + uint64_log2(ds[sz-1]);
    else
        return (sz - 1)*32 + ::log2(static_cast<unsigned>(ds[sz-1]));
#else
    unsigned r = mpz_sizeinbase(*a.m_ptr, 2);
    SASSERT(r > 0);
    return r - 1;
#endif
}

template<bool SYNCH>
unsigned mpz_manager<SYNCH>::mlog2(mpz const & a) {
    if (is_nonneg(a))
        return 0;
    if (is_small(a))
        return ::log2((unsigned)-a.m_val);
#ifndef _MP_GMP
    static_assert(sizeof(digit_t) == 8 || sizeof(digit_t) == 4, "");
    mpz_cell * c     = a.m_ptr;
    unsigned sz      = c->m_size;
    digit_t * ds     = c->m_digits; 
    if (sizeof(digit_t) == 8)
        return (sz - 1)*64 + uint64_log2(ds[sz-1]);
    else
        return (sz - 1)*32 + ::log2(static_cast<unsigned>(ds[sz-1]));
#else
    mpz_neg(m_tmp, *a.m_ptr);
    unsigned r = mpz_sizeinbase(m_tmp, 2);
    SASSERT(r > 0);
    return r - 1;
#endif
}

template<bool SYNCH>
unsigned mpz_manager<SYNCH>::bitsize(mpz const & a) {
    if (is_nonneg(a)) 
        return log2(a) + 1;
    else
        return mlog2(a) + 1;
}

template<bool SYNCH>
bool mpz_manager<SYNCH>::is_perfect_square(mpz const & a, mpz & root) {
    if (is_neg(a))
        return false;
    reset(root);
    if (is_zero(a)) {
        return true;
    }
    if (is_one(a)) {
        set(root, 1);
        return true;
    }

    mpz lo, hi, mid, sq_lo, sq_hi, sq_mid;
    set(lo, 1);
    set(hi, a);
    set(sq_lo, 1);
    mul(hi, hi, sq_hi);
    bool result;
    // lo*lo <= *this < hi*hi
    while (true) {
        SASSERT(lt(lo, hi));
        SASSERT(le(sq_lo, a) && lt(a, sq_hi));
        if (eq(sq_lo, a)) {
            set(root, lo);
            result = true;
            break;
        }

        mpz & tmp = mid;
        add(lo, mpz(1), tmp);
        if (eq(tmp, hi)) {
            set(root, hi);
            result = false;
            break;
        }
        
        add(hi, lo, tmp);
        div(tmp, mpz(2), mid);
        
        SASSERT(lt(lo, mid) && lt(mid, hi));
        
        mul(mid, mid, sq_mid);

        if (gt(sq_mid, a)) {
            set(hi, mid);
            set(sq_hi, sq_mid);
        }
        else {
            set(lo, mid);
            set(sq_lo, sq_mid);
        }
    }
    del(lo);
    del(hi);
    del(mid);
    del(sq_lo);
    del(sq_hi);
    del(sq_mid);
    return result;
}


static unsigned div_l(unsigned k, unsigned n) {
    return k/n;
}

static unsigned div_u(unsigned k, unsigned n) {
    return k%n == 0 ? k/n : k/n + 1;
}

template<bool SYNCH>
bool mpz_manager<SYNCH>::root(mpz & a, unsigned n) {
    SASSERT(n % 2 != 0 || is_nonneg(a));
    if (is_zero(a)) {
        return true; // precise
    }
    
    // Initial approximation
    //
    // We have that:
    // a >  0 ->    2^{log2(a)}     <= a <= 2^{(log2(a) + 1)}
    // a <  0 ->   -2^{log2(a) + 1} <= a <= -2^{log2(a)}
    //
    // Thus
    // a >  0 ->    2^{div_l(log2(a), n)}     <= a^{1/n} <=  2^{div_u(log2(a) + 1, n)}
    // a <  0 ->   -2^{div_u(log2(a) + 1, n)} <= a^{1/n} <= -2^{div_l(log2(a), n)}
    //
    mpz lower;
    mpz upper;
    mpz mid;
    mpz mid_n;
    
    if (is_pos(a)) {
        unsigned k = log2(a);
        power(mpz(2), div_l(k, n),     lower);
        power(mpz(2), div_u(k + 1, n), upper);
    }
    else {
        unsigned k = mlog2(a);
        power(mpz(2), div_u(k + 1, n), lower);
        power(mpz(2), div_l(k, n),     upper);
        neg(lower);
        neg(upper);
    }

    bool result;
    SASSERT(le(lower, upper));
    if (eq(lower, upper)) {
        swap(a, lower);
        result = true;
    }
    else {
        // Refine using bisection. TODO: use Newton's method if this is a bottleneck
        while (true) {
            add(upper, lower, mid);
            machine_div2k(mid, 1);
            TRACE("mpz", tout << "upper: "; display(tout, upper); tout << "\nlower: "; display(tout, lower); tout << "\nmid: "; display(tout, mid); tout << "\n";);
            power(mid, n, mid_n);
            if (eq(mid_n, a)) {
                swap(a, mid);
                result = true;
                break;
            }
            if (eq(mid, lower) || eq(mid, upper)) {
                swap(a, upper);
                result = false;
                break;
            }
            if (lt(mid_n, a)) {
                // new lower bound
                swap(mid, lower);
            }
            else {
                SASSERT(lt(a, mid_n));
                // new upper bound
                swap(mid, upper);
            }
        }
    }
    del(lower);
    del(upper);
    del(mid);
    del(mid_n);
    return result;
}

template<bool SYNCH>
bool mpz_manager<SYNCH>::decompose(mpz const & a, svector<digit_t> & digits) {
    digits.reset();
    if (is_small(a)) {
        if (a.m_val < 0) {
            digits.push_back(-a.m_val);
            return true;
        }
        else {
            digits.push_back(a.m_val);
            return false;
        }
    }
    else {
#ifndef _MP_GMP
        mpz_cell * cell_a = a.m_ptr;
        unsigned sz = cell_a->m_size;
        for (unsigned i = 0; i < sz; i++) {
            digits.push_back(cell_a->m_digits[i]);
        }
        return a.m_val < 0;
#else
    bool r = is_neg(a);
    mpz_set(m_tmp, *a.m_ptr);
    mpz_abs(m_tmp, m_tmp);
    while (mpz_sgn(m_tmp) != 0) {
      mpz_tdiv_r_2exp(m_tmp2, m_tmp, 32);
      unsigned v = mpz_get_ui(m_tmp2);
      digits.push_back(v);
      mpz_tdiv_q_2exp(m_tmp, m_tmp, 32);
    }
    return r;
#endif
    }
}

template<bool SYNCH>
bool mpz_manager<SYNCH>::divides(mpz const & a, mpz const & b) {
    _scoped_numeral<mpz_manager<SYNCH> > tmp(*this);
    bool r;
    if (is_zero(a)) {
        // I assume 0 | 0. 
        // Remark a|b is a shorthand for (exists x. a x = b)
        // If b is zero, any x will do. If b != 0, then a does not divide b
        r = is_zero(b);
    }
    else {
        rem(b, a, tmp);
        r = is_zero(tmp);
    }
    STRACE("divides", tout << "[mpz] Divisible["; display(tout, b); tout << ", "; display(tout, a); tout << "] == " << (r?"True":"False") << "\n";);
    TRACE("divides_bug", tout << "tmp: "; display(tout, tmp); tout << "\n";);
    return r;
}

template class mpz_manager<true>;
template class mpz_manager<false>;
