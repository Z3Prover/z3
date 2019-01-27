/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    mpfx.h

Abstract:

    Multi precision fixed point numbers.
    
Author:

    Leonardo de Moura (leonardo) 2012-09-19

Revision History:

--*/
#include<sstream>
#include<iomanip>
#include "util/mpfx.h"
#include "util/mpn.h"
#include "util/mpz.h"
#include "util/mpq.h"
#include "util/bit_util.h"
#include "util/trace.h"

mpfx_manager::mpfx_manager(unsigned int_sz, unsigned frac_sz, unsigned initial_capacity) {
    SASSERT(initial_capacity > 0);
    SASSERT(int_sz > 0);
    SASSERT(frac_sz > 0);
    m_int_part_sz  = int_sz;
    m_frac_part_sz = frac_sz;
    m_total_sz     = m_int_part_sz + m_frac_part_sz;
    m_words.resize(initial_capacity * m_total_sz, 0);
    m_capacity     = initial_capacity;
    m_to_plus_inf  = false;
    m_buffer0.resize(2*m_total_sz, 0);
    m_buffer1.resize(2*m_total_sz, 0);
    m_buffer2.resize(2*m_total_sz, 0);
    VERIFY(m_id_gen.mk() == 0);
    set(m_one, 1);
}

mpfx_manager::~mpfx_manager() {
    del(m_one);
}

void mpfx_manager::expand() {
    m_capacity = 2*m_capacity;
    m_words.resize(m_capacity * m_total_sz, 0);
}

void mpfx_manager::allocate(mpfx & n) {
    SASSERT(n.m_sig_idx == 0);
    unsigned sig_idx = m_id_gen.mk();
    ensure_capacity(sig_idx);
    n.m_sig_idx = sig_idx;
    SASSERT(::is_zero(m_total_sz, words(n)));
}

unsigned mpfx_manager::sz(unsigned * ws) const { 
    SASSERT(!::is_zero(m_total_sz, ws));
    unsigned r = m_total_sz; 
    while (true) { 
        SASSERT(r > 0);
        --r; 
        if (ws[r] != 0) 
            return r + 1; 
    }
}

void mpfx_manager::del(mpfx & n) {
    unsigned sig_idx = n.m_sig_idx;
    if (sig_idx != 0) {
        m_id_gen.recycle(sig_idx);
        unsigned * w = words(n);
        for (unsigned i = 0; i < m_total_sz; i++)
            w[i] = 0;
    }
}

void mpfx_manager::reset(mpfx & n) {
    del(n);
    n.m_sign     = false;
    n.m_sig_idx  = 0;
    SASSERT(check(n));
}

bool mpfx_manager::is_int(mpfx const & n) const {
    unsigned * w = words(n);
    for (unsigned i = 0; i < m_frac_part_sz; i++)
        if (w[i] != 0)
            return false;
    return true;
}

bool mpfx_manager::is_abs_one(mpfx const & n) const {
    unsigned * w = words(n);
    return is_int(n) && w[m_frac_part_sz] == 1 && ::is_zero(m_int_part_sz - 1, w + m_frac_part_sz + 1);
}

bool mpfx_manager::is_int64(mpfx const & a) const {
    if (!is_int(a))
        return false;
    if (is_zero(a) || m_int_part_sz <= 1)
        return true;
    unsigned * w = words(a);
    w += m_frac_part_sz;
    if (w[1] < 0x80000000u || (w[1] == 0x80000000u && is_neg(a))) {
        for (unsigned i = 2; i < m_int_part_sz; i++)
            if (w[i] != 0)
                return false;
        return true;
    }
    else {
        return false;
    }
}

bool mpfx_manager::is_uint64(mpfx const & a) const {
    if (!is_int(a) || is_neg(a))
        return false;
    if (is_zero(a) || m_int_part_sz <= 2)
        return true;
    unsigned * w = words(a);
    for (unsigned i = m_frac_part_sz + 2; i < m_total_sz; i++)
        if (w[i] != 0)
            return false;
    return true;
}

void mpfx_manager::set(mpfx & n, int v) {
    if (v == 0) {
        reset(n);
    }
    else {
        if (v < 0) {
            set(n, static_cast<unsigned>(-v));
            n.m_sign = 1;
        }
        else {
            set(n, static_cast<unsigned>(v));
        }
    }
    SASSERT(get_int64(n) == v);
    SASSERT(check(n));
}

void mpfx_manager::set(mpfx & n, unsigned v) {
    if (v == 0) {
        reset(n);
    }
    else {
        allocate_if_needed(n);
        n.m_sign              = 0;
        unsigned * w          = words(n);
        for (unsigned i = 0; i < m_total_sz; i++) 
            w[i] = 0;
        w[m_frac_part_sz]     = v;
    }
    SASSERT(is_int(n));
    SASSERT(get_uint64(n) == v);
    SASSERT(check(n));
}

void mpfx_manager::set(mpfx & n, int64_t v) {
    if (m_int_part_sz == 1) {
        if (v < -static_cast<int64_t>(static_cast<uint64_t>(UINT_MAX)) ||
            v > static_cast<int64_t>(static_cast<uint64_t>(UINT_MAX)))
            throw overflow_exception();
    }
    if (v == 0) {
        reset(n);
    }
    else {
        if (v < 0) {
            set(n, static_cast<uint64_t>(-v));
            n.m_sign = 1;
        }
        else {
            set(n, static_cast<uint64_t>(v));
        }
    }
    SASSERT(is_int(n));
    SASSERT(get_int64(n) == v);
    SASSERT(check(n));
}

void mpfx_manager::set(mpfx & n, uint64_t v) {
    if (m_int_part_sz == 1) {
        if (v > static_cast<uint64_t>(UINT_MAX))
            throw overflow_exception();
    }

    if (v == 0) {
        reset(n);
    }
    else {
        allocate_if_needed(n);
        n.m_sign              = 0;
        unsigned * w          = words(n);
        uint64_t * _vp        = &v;
        unsigned * _v         = nullptr;
        memcpy(&_v, &_vp, sizeof(unsigned*));
        for (unsigned i = 0; i < m_total_sz; i++) 
            w[i] = 0;
        w[m_frac_part_sz]     = _v[0];
        if (m_int_part_sz == 1) {
            SASSERT(_v[1] == 0);
        }
        else {
            w[m_frac_part_sz+1] = _v[1];
        }
    }
    SASSERT(is_int(n));
    SASSERT(get_uint64(n) == v);
    SASSERT(check(n));
}

void mpfx_manager::set(mpfx & n, int num, unsigned den) {
    scoped_mpfx a(*this), b(*this);
    set(a, num);
    set(b, den);
    div(a, b, n);
    SASSERT(check(n));
}

void mpfx_manager::set(mpfx & n, int64_t num, uint64_t den) {
    scoped_mpfx a(*this), b(*this);
    set(a, num);
    set(b, den);
    div(a, b, n);
    SASSERT(check(n));
}

void mpfx_manager::set(mpfx & n, mpfx const & v) {
    if (is_zero(v)) {
        reset(n);
        return;
    }
    allocate_if_needed(n);
    n.m_sign      = v.m_sign;
    unsigned * w1 = words(n);
    unsigned * w2 = words(v);
    for (unsigned i = 0; i < m_total_sz; i++)
        w1[i] = w2[i];
    SASSERT(check(n));
}

template<bool SYNCH>
void mpfx_manager::set_core(mpfx & n, mpz_manager<SYNCH> & m, mpz const & v) {
    if (m.is_zero(v)) {
        reset(n);
    }
    else {
        m_tmp_digits.reset();
        allocate_if_needed(n);
        n.m_sign = m.decompose(v, m_tmp_digits);
        unsigned sz = m_tmp_digits.size();
        if (sz > m_int_part_sz)
            throw overflow_exception();
        unsigned * w = words(n);
        for (unsigned i = 0; i < m_frac_part_sz; i++) 
            w[i] = 0;
        ::copy(sz, m_tmp_digits.c_ptr(), m_int_part_sz, w + m_frac_part_sz);
    }
    SASSERT(check(n));
}

void mpfx_manager::set(mpfx & n, unsynch_mpz_manager & m, mpz const & v) {
    set_core(n, m, v);
}

#ifndef _NO_OMP_
void mpfx_manager::set(mpfx & n, synch_mpz_manager & m, mpz const & v) {
    set_core(n, m, v);
}
#endif

template<bool SYNCH>
void mpfx_manager::set_core(mpfx & n, mpq_manager<SYNCH> & m, mpq const & v) {
    if (m.is_int(v)) {
        set_core(n, m, v.numerator());
    }
    else {
        allocate_if_needed(n);
        _scoped_numeral<mpz_manager<SYNCH> > tmp(m);
        n.m_sign = is_neg(n);
        m.mul2k(v.numerator(), 8 * sizeof(unsigned) * m_frac_part_sz, tmp);
        m.abs(tmp);
        if ((n.m_sign == 1) != m_to_plus_inf && !m.divides(v.denominator(), tmp)) {
            m.div(tmp, v.denominator(), tmp);
            m.inc(tmp);
        }
        else {
            m.div(tmp, v.denominator(), tmp);
        }
        m_tmp_digits.reset();
        m.decompose(tmp, m_tmp_digits);
        unsigned sz = m_tmp_digits.size();
        if (sz > m_total_sz)
            throw overflow_exception();
        unsigned * w = words(n);
        ::copy(sz, m_tmp_digits.c_ptr(), m_total_sz, w);
    }
    SASSERT(check(n));
}

void mpfx_manager::set(mpfx & n, unsynch_mpq_manager & m, mpq const & v) {
    set_core(n, m, v);
}

#ifndef _NO_OMP_
void mpfx_manager::set(mpfx & n, synch_mpq_manager & m, mpq const & v) {
    set_core(n, m, v);
}
#endif

bool mpfx_manager::eq(mpfx const & a, mpfx const & b) const {
    if (is_zero(a) && is_zero(b))
        return true;
    if (is_zero(a) || is_zero(b))
        return false;
    if (a.m_sign     != b.m_sign) 
        return false;
    unsigned * w1 = words(a);
    unsigned * w2 = words(b);
    for (unsigned i = 0; i < m_total_sz; i++) 
        if (w1[i] != w2[i])
            return false;
    return true;
}

bool mpfx_manager::lt(mpfx const & a, mpfx const & b) const {
    STRACE("mpfx_trace", tout << "[mpfx] ("; display(tout, a); tout << " < "; display(tout, b); tout << ") == ";);
    bool r;
    if (is_zero(a)) {
        r = !is_zero(b) && !is_neg(b);
    }
    else if (is_zero(b)) {
        r = is_neg(a);
    }
    else {
        SASSERT(!is_zero(a));
        SASSERT(!is_zero(b));
        if (is_neg(a)) {
            r = is_pos(b) || ::lt(m_total_sz, words(b), words(a));
        }
        else {
            SASSERT(is_pos(a));
            r = is_pos(b) && ::lt(m_total_sz, words(a), words(b));
        }
    }
    STRACE("mpfx_trace", tout << "(" << r << " == 1)\n";);
    return r;
}

void mpfx_manager::add_sub(bool is_sub, mpfx const & a, mpfx const & b, mpfx & c) {
    if (is_zero(a)) {
        set(c, b);
        if (is_sub)
            neg(c);
        return;
    }

    if (is_zero(b)) {
        set(c, a);
        return;
    }

    TRACE("mpfx", tout << (is_sub ? "sub" : "add") << "("; display(tout, a); tout << ", "; display(tout, b); tout << ")\n";);

    allocate_if_needed(c);

    bool sgn_a = a.m_sign;
    bool sgn_b = b.m_sign;
    unsigned * w_a = words(a);
    unsigned * w_b = words(b);

    if (is_sub)
        sgn_b = !sgn_b;

    // Compute c
    unsigned * w_c = words(c);
    if (sgn_a == sgn_b) {
        c.m_sign = sgn_a;
        if (!::add(m_total_sz, w_a, w_b, w_c))
            throw overflow_exception();
    }
    else {
        unsigned borrow;
        SASSERT(sgn_a != sgn_b);
        if (::lt(m_total_sz, w_a, w_b)) {
            c.m_sign = sgn_b;
            m_mpn_manager.sub(w_b, m_total_sz, w_a, m_total_sz, w_c, &borrow);
            SASSERT(!::is_zero(m_total_sz, w_c));
        }
        else {
            c.m_sign = sgn_a;
            m_mpn_manager.sub(w_a, m_total_sz, w_b, m_total_sz, w_c, &borrow);
            if (::is_zero(m_total_sz, w_c))
                reset(c);
        }
        SASSERT(borrow == 0);
    }
    TRACE("mpfx", tout << "result: "; display(tout, c); tout << "\n";);
    SASSERT(check(c));
}

void mpfx_manager::add(mpfx const & a, mpfx const & b, mpfx & c) {
    STRACE("mpfx_trace", tout << "[mpfx] "; display(tout, a); tout << " + "; display(tout, b); tout << " == ";);
    add_sub(false, a, b, c);
    STRACE("mpfx_trace", display(tout, c); tout << "\n";);  
}

void mpfx_manager::sub(mpfx const & a, mpfx const & b, mpfx & c) {
    STRACE("mpfx_trace", tout << "[mpfx] "; display(tout, a); tout << " - "; display(tout, b); tout << " == ";);
    add_sub(true, a, b, c);
    STRACE("mpfx_trace", display(tout, c); tout << "\n";);  
}

void mpfx_manager::mul(mpfx const & a, mpfx const & b, mpfx & c) {
    STRACE("mpfx_trace", tout << "[mpfx] ("; display(tout, a); tout << ") * ("; display(tout, b); tout << ") " << (m_to_plus_inf ? "<=" : ">=") << " ";);
    if (is_zero(a) || is_zero(b)) {
        reset(c);
    }
    else {
        allocate_if_needed(c);
        c.m_sign      = a.m_sign ^ b.m_sign;
        unsigned * r  = m_buffer0.c_ptr();
        m_mpn_manager.mul(words(a), m_total_sz, words(b), m_total_sz, r);
        // round result
        unsigned * _r = r + m_frac_part_sz;
        if ((c.m_sign == 1) != m_to_plus_inf && !::is_zero(m_frac_part_sz, r)) {
            if (!::inc(m_total_sz, _r))
                throw overflow_exception();
        }
        // check for overflows
        if (!::is_zero(m_int_part_sz, _r + m_total_sz))
            throw overflow_exception();
        // copy result to c
        unsigned * w_c = words(c);
        for (unsigned i = 0; i < m_total_sz; i++)
            w_c[i] = _r[i];
    }
    STRACE("mpfx_trace", display(tout, c); tout << "\n";);  
    SASSERT(check(c));
}

void mpfx_manager::div(mpfx const & a, mpfx const & b, mpfx & c) {
    if (is_zero(b)) 
        throw div0_exception();
    STRACE("mpfx_trace", tout << "[mpfx] ("; display(tout, a); tout << ") / ("; display(tout, b); tout << ") " << (m_to_plus_inf ? "<=" : ">=") << " ";);
    if (is_zero(a)) {
        reset(c);
    }
    else {
        allocate_if_needed(c);
        c.m_sign    = a.m_sign ^ b.m_sign;
        unsigned * w_a       = words(a);
        unsigned * w_a_shft  = m_buffer0.c_ptr();
        unsigned a_shft_sz   = sz(w_a) + m_frac_part_sz; 
        // copy a to buffer 0, and shift by m_frac_part_sz
        for (unsigned i = 0; i < m_frac_part_sz; i++) 
            w_a_shft[i] = 0;
        for (unsigned i = 0; i < m_total_sz; i++)
            w_a_shft[i+m_frac_part_sz] = w_a[i];
        unsigned * w_b       = words(b);
        unsigned b_sz        = sz(w_b);
        unsigned * w_q       = m_buffer1.c_ptr();
        if (b_sz > a_shft_sz) {
            if ((c.m_sign == 1) != m_to_plus_inf)
                set_epsilon(c);
            else
                reset(c);
        }
        else {
            unsigned q_sz        = a_shft_sz - b_sz + 1; 
            unsigned * w_r       = m_buffer2.c_ptr();
            unsigned r_sz        = b_sz;
            m_mpn_manager.div(w_a_shft, a_shft_sz,
                              w_b,      b_sz,
                              w_q, 
                              w_r);
            for (unsigned i = m_total_sz; i < q_sz; i++)
                if (w_q[i] != 0)
                    throw overflow_exception();
            if  (((c.m_sign == 1) != m_to_plus_inf) && !::is_zero(r_sz, w_r)) {
                // round the result
                if (!::inc(m_total_sz, w_q))
                    throw overflow_exception();
            }
            unsigned * w_c = words(c);
            bool zero_q = true;
            if (m_total_sz >= q_sz) {
                unsigned i;
                for (i = 0; i < q_sz; i++)  {
                    if (w_q[i] != 0)
                        zero_q = false;
                    w_c[i] = w_q[i];
                }
                for (; i < m_total_sz; i++) 
                    w_c[i] = 0;
            }
            else {
                for (unsigned i = 0; i < m_total_sz; i++) {
                    if (w_q[i] != 0)
                        zero_q = false;
                    w_c[i] = w_q[i];
                }
            }
            if (zero_q) {
                if ((c.m_sign == 1) != m_to_plus_inf)
                    set_epsilon(c);
                else
                    reset(c);
            }
        }
    }
    STRACE("mpfx_trace", display(tout, c); tout << "\n";);  
    SASSERT(check(c));
}

void mpfx_manager::div2k(mpfx & a, unsigned k) {
    STRACE("mpfx_trace", tout << "[mpfx] ("; display(tout, a); tout << ") / (2^" << k << ") " << (m_to_plus_inf ? "<=" : ">=") << " ";);
    if (!is_zero(a) && k > 0) {
        unsigned * w = words(a);
        bool _inc = ((a.m_sign == 1) != m_to_plus_inf) && has_one_at_first_k_bits(m_total_sz, w, k);
        shr(m_total_sz, w, k, m_total_sz, w);
        if (_inc) {
            VERIFY(::inc(m_total_sz, w));
            SASSERT(!::is_zero(m_total_sz, w));
        }
        else if (::is_zero(m_total_sz, w)) {
            reset(a);
        }
    }
    STRACE("mpfx_trace", display(tout, a); tout << "\n";);  
    SASSERT(check(a));
}

void mpfx_manager::set_epsilon(mpfx & n) {
    unsigned * w = words(n);
    w[0] = 1;
    for (unsigned i = 1; i < m_total_sz; i++)
        w[i] = 0;
}

void mpfx_manager::set_minus_epsilon(mpfx & n) {
    set_epsilon(n);
    n.m_sign = true;
    SASSERT(check(n));
}

void mpfx_manager::set_plus_epsilon(mpfx & n) {
    set_epsilon(n);
    n.m_sign = 0;
    SASSERT(check(n));
}

void mpfx_manager::floor(mpfx & n) {
    STRACE("mpfx_trace", tout << "[mpfx] Floor["; display(tout, n); tout << "] == ";);
    unsigned * w = words(n);
    if (is_neg(n)) {
        bool is_int = true;
        for (unsigned i = 0; i < m_frac_part_sz; i++) {
            if (w[i] != 0) {
                is_int = false;
                w[i] = 0;
            }
        }
        if (!is_int && !::inc(m_int_part_sz, w + m_frac_part_sz))
            throw overflow_exception();
    }
    else {
        for (unsigned i = 0; i < m_frac_part_sz; i++)
            w[i] = 0;
    }
    if (::is_zero(m_int_part_sz, w + m_frac_part_sz))
        reset(n);
    SASSERT(check(n));
    STRACE("mpfx_trace", display(tout, n); tout << "\n";);  
}

void mpfx_manager::ceil(mpfx & n) {
    STRACE("mpfx_trace", tout << "[mpfx] Ceiling["; display(tout, n); tout << "] == ";);
    unsigned * w = words(n);
    if (is_pos(n)) {
        bool is_int = true;
        for (unsigned i = 0; i < m_frac_part_sz; i++) {
            if (w[i] != 0) {
                is_int = false;
                w[i] = 0;
            }
        }
        if (!is_int && !::inc(m_int_part_sz, w + m_frac_part_sz))
            throw overflow_exception();
    }
    else {
        for (unsigned i = 0; i < m_frac_part_sz; i++)
            w[i] = 0;
    }
    if (::is_zero(m_int_part_sz, w + m_frac_part_sz))
        reset(n);
    SASSERT(check(n));
    STRACE("mpfx_trace", display(tout, n); tout << "\n";);  
}

void mpfx_manager::power(mpfx const & a, unsigned p, mpfx & b) {
#ifdef _TRACE
    scoped_mpfx _a(*this); _a = a;
    unsigned _p = p;
#endif
#define SMALL_POWER 8
    SASSERT(check(a));
    if (is_zero(a)) {
        SASSERT(p != 0);
        reset(b);
    }
    else if (p == 0) {
        set(b, 1);
    }
    else if (p == 1) {
        set(b, a);
    }
    else if (p == 2) {
        mul(a, a, b);
    }
    else if (p <= SMALL_POWER && &a != &b) {
        SASSERT(p > 2);
        --p;
        set(b, a);
        while (p > 0) {
            --p;
            mul(a, b, b);
        }
    }
    else {
        unsigned mask = 1;
        scoped_mpfx pw(*this);
        set(pw, a);
        set(b, 1);
        while (mask <= p) {
            if (mask & p)
                mul(b, pw, b);
            mul(pw, pw, pw);
            mask = mask << 1;
        }
    }
    STRACE("mpfx_trace", tout << "[mpfx] ("; display(tout, _a); tout << ") ^ " << _p << (m_to_plus_inf ? "<=" : ">="); display(tout, b); tout << "\n";);
    TRACE("mpfx_power", display_raw(tout, b); tout << "\n";);
    SASSERT(check(b));
}


bool mpfx_manager::is_power_of_two(mpfx const & a, unsigned & k) const {
    if (!is_int(a) || is_zero(a))
        return false;
    unsigned * w = words(a);
    unsigned i   = m_total_sz;
    while (true) {
        SASSERT (i > m_frac_part_sz);
        --i;
        if (w[i] != 0) {
            if (!::is_power_of_two(w[i]))
                return false;
            k = (i - m_frac_part_sz) * 8 * sizeof(unsigned) + log2(w[i]);
            while (i > m_frac_part_sz) {
                --i;
                if (w[i] != 0)
                    return false;
            }
            return true;
        }
    }
}

bool mpfx_manager::is_power_of_two(mpfx const & a) const {
    unsigned k;
    return is_power_of_two(a, k);
}

int64_t mpfx_manager::get_int64(mpfx const & n) const {
    SASSERT(is_int64(n));
    unsigned * w = words(n);
    w += m_frac_part_sz;
    uint64_t r = 0;
    memcpy(&r, w, sizeof(uint64_t));
    if (r == 0x8000000000000000ull) {
        SASSERT(is_neg(n));
        return INT64_MIN;
    }
    else {
        return is_neg(n) ? -static_cast<int64_t>(r) : r;
    }
}

uint64_t mpfx_manager::get_uint64(mpfx const & n) const {
    SASSERT(is_uint64(n));
    unsigned * w = words(n);
    w += m_frac_part_sz;
    uint64_t r = 0;
    memcpy(&r, w, sizeof(uint64_t));
    return r;
}

template<bool SYNCH>
void mpfx_manager::to_mpz_core(mpfx const & n, mpz_manager<SYNCH> & m, mpz & t) {
    SASSERT(is_int(n));
    unsigned * w = words(n);
    m.set_digits(t, m_int_part_sz, w+m_frac_part_sz);
    if (is_neg(n))
        m.neg(t);
}

void mpfx_manager::to_mpz(mpfx const & n, unsynch_mpz_manager & m, mpz & t) {
    to_mpz_core(n, m, t);
}

#ifndef _NO_OMP_
void mpfx_manager::to_mpz(mpfx const & n, synch_mpz_manager & m, mpz & t) {
    to_mpz_core(n, m, t);
}
#endif

template<bool SYNCH>
void mpfx_manager::to_mpq_core(mpfx const & n, mpq_manager<SYNCH> & m, mpq & t) {
    _scoped_numeral<mpz_manager<SYNCH> > a(m), b(m);

    unsigned * w = words(n);
    m.set(a, m_total_sz, w);

    m.set(b, 1);
    m.mul2k(b, sizeof(unsigned)*8*m_frac_part_sz);

    m.rat_div(a, b, t);

    if (is_neg(n))
        m.neg(t);
}

void mpfx_manager::to_mpq(mpfx const & n, unsynch_mpq_manager & m, mpq & t) {
    to_mpq_core(n, m, t);
}

#ifndef _NO_OMP_
void mpfx_manager::to_mpq(mpfx const & n, synch_mpq_manager & m, mpq & t) {
    to_mpq_core(n, m, t);
}
#endif

void mpfx_manager::display_raw(std::ostream & out, mpfx const & n) const {
    if (is_neg(n))
        out << "-";
    unsigned * w = words(n);
    unsigned i   = m_total_sz;
    while(i > 0) {
        if (i == m_frac_part_sz)
            out << ".";
        --i;
        out << std::hex << std::setfill('0') << std::setw(2 * sizeof(unsigned)) << w[i];
    }
}

void mpfx_manager::display(std::ostream & out, mpfx const & n) const {
    if (is_neg(n))
        out << "-";
    unsigned * w   = words(n);
    unsigned sz    = m_total_sz;
    unsigned shift = UINT_MAX;
    if (is_int(n)) {
        w  += m_frac_part_sz;
        sz -= m_frac_part_sz;
    }
    else {
        shift = ntz(m_total_sz, w);
        if (shift > 0)
            shr(m_total_sz, w, shift, m_total_sz, w);
    }

    sbuffer<char, 1024> str_buffer(11*sz, 0);
    out << m_mpn_manager.to_string(w, sz, str_buffer.begin(), str_buffer.size());
    if (!is_int(n)) {
        SASSERT(shift != UINT_MAX);
        // reverse effect of shr
        if (shift > 0)
            shl(m_total_sz, w, shift, m_total_sz, w);
        // display denominator as a power of 2
        unsigned k = sizeof(unsigned)*8*m_frac_part_sz - shift;
        out << "/2";
        if (k > 1)
            out << "^" << k;
    }
}

void mpfx_manager::display_smt2(std::ostream & out, mpfx const & n) const {
    if (is_neg(n))
        out << "(- ";
    unsigned * w = words(n);
    unsigned sz  = m_total_sz;
    if (is_int(n)) {
        w  += m_frac_part_sz;
        sz -= m_frac_part_sz;
    }
    else {
        out << "(/ ";
    }
    sbuffer<char, 1024> str_buffer(11*sz, 0);
    out << m_mpn_manager.to_string(w, sz, str_buffer.begin(), str_buffer.size());
    if (!is_int(n)) {
        out << " ";
        unsigned * w = m_buffer0.c_ptr();
        for (unsigned i = 0; i < m_frac_part_sz; i++)
            w[i] = 0;
        w[m_frac_part_sz] = 1;
        sbuffer<char, 1024> str_buffer2(11*(m_frac_part_sz+1), 0);
        out << m_mpn_manager.to_string(w, m_frac_part_sz + 1, str_buffer2.begin(), str_buffer2.size());
        out << ")";
    }
    if (is_neg(n))
        out << ")";
}

void mpfx_manager::display_decimal(std::ostream & out, mpfx const & n, unsigned prec) const {
    if (is_neg(n))
        out << "-";
    unsigned * w = words(n);
    sbuffer<char, 1024> str_buffer(11*m_int_part_sz, 0);
    out << m_mpn_manager.to_string(w + m_frac_part_sz, m_int_part_sz, str_buffer.begin(), str_buffer.size());
    if (!is_int(n)) {
        out << ".";
        unsigned * frac   = m_buffer0.c_ptr();
        ::copy(m_frac_part_sz, w, m_frac_part_sz, frac);
        unsigned ten      = 10;
        unsigned * n_frac = m_buffer1.c_ptr();
        bool frac_is_zero = false;
        unsigned i        = 0;
        while (!frac_is_zero) {
            if (i >= prec) {
                out << "?";
                return;
            }
            m_mpn_manager.mul(frac, m_frac_part_sz, &ten, 1, n_frac);
            frac_is_zero = ::is_zero(m_frac_part_sz, n_frac);
            SASSERT(n_frac[m_frac_part_sz] <= 9);
            if (!frac_is_zero || n_frac[m_frac_part_sz] != 0)
                out << n_frac[m_frac_part_sz];
            n_frac[m_frac_part_sz] = 0;
            std::swap(frac, n_frac);
            i++;
        }
    }
}

std::string mpfx_manager::to_string(mpfx const & a) const {
    std::ostringstream buffer;
    display(buffer, a);
    return buffer.str();
}

std::string mpfx_manager::to_rational_string(mpfx const & a) const {
    return to_string(a);
}

bool mpfx_manager::check(mpfx const & a) const {
    SASSERT(!is_zero(a) || a.m_sign == 0);
    SASSERT(is_zero(a) == ::is_zero(m_total_sz, words(a)));
    return true;
}

unsigned mpfx_manager::prev_power_of_two(mpfx const & a) {
    if (!is_pos(a))
        return 0;
    return m_int_part_sz * sizeof(unsigned) * 8 - nlz(m_int_part_sz, words(a) + m_frac_part_sz) - 1;
}
