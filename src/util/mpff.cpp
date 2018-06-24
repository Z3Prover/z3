/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    mpff.cpp

Abstract:

    Multi precision fast floating point numbers.
    The implementation is not compliant with the IEEE standard.
    For a compliant implementation, see mpf.h
    
Author:

    Leonardo de Moura (leonardo) 2012-09-12

Revision History:

--*/
#include<sstream>
#include<iomanip>
#include "util/mpff.h"
#include "util/mpn.h"
#include "util/mpz.h"
#include "util/mpq.h"
#include "util/bit_util.h"
#include "util/trace.h"

static_assert(sizeof(mpn_digit) == sizeof(unsigned), "");
static_assert(sizeof(unsigned)  == 4, "unsigned haven't changed size for a while");

// MIN_MSW is an shorthand for 0x8000..00, i.e., the minimal most significand word.
#define MIN_MSW (1u << (sizeof(unsigned) * 8 - 1))

mpff_manager::mpff_manager(unsigned prec, unsigned initial_capacity) {
    SASSERT(initial_capacity > 0);
    m_precision      = prec;
    m_precision_bits = prec * 8 * sizeof(unsigned);
    m_capacity       = initial_capacity;
    m_to_plus_inf    = false;
    m_significands.resize(initial_capacity * prec, 0);
    for (unsigned i = 0; i < MPFF_NUM_BUFFERS; i++)
        m_buffers[i].resize(2 * prec, 0);
    // Reserve space for zero
    VERIFY(m_id_gen.mk() == 0);
    set(m_one, 1);
}

mpff_manager::~mpff_manager() {
    del(m_one);
}

void mpff_manager::expand() {
    m_capacity = 2*m_capacity;
    m_significands.resize(m_capacity * m_precision, 0);
}

void mpff_manager::allocate(mpff & n) {
    SASSERT(n.m_sig_idx == 0);
    unsigned sig_idx = m_id_gen.mk();
    ensure_capacity(sig_idx);
    n.m_sig_idx = sig_idx;
    DEBUG_CODE({
            unsigned * s = sig(n);
            for (unsigned i = 0; i < m_precision; i++) {
                SASSERT(s[i] == 0);
            }
        });
}

void mpff_manager::to_buffer(unsigned idx, mpff const & n) const {
    SASSERT(idx < MPFF_NUM_BUFFERS);
    svector<unsigned> & b = const_cast<mpff_manager*>(this)->m_buffers[idx];
    unsigned * s = sig(n);
    for (unsigned i = 0; i < m_precision; i++)
        b[i] = s[i];
}

void mpff_manager::to_buffer_ext(unsigned idx, mpff const & n) const {
    SASSERT(idx < MPFF_NUM_BUFFERS);
    svector<unsigned> & b = const_cast<mpff_manager*>(this)->m_buffers[idx];
    unsigned * s = sig(n);
    unsigned j = m_precision;
    for (unsigned i = 0; i < m_precision; i++, j++) {
        b[i] = s[i];
        b[j] = 0;
    }
}

void mpff_manager::to_buffer_shifting(unsigned idx, mpff const & n) const {
    SASSERT(idx < MPFF_NUM_BUFFERS);
    svector<unsigned> & b = const_cast<mpff_manager*>(this)->m_buffers[idx];
    unsigned * s = sig(n);
    unsigned j   = m_precision;
    for (unsigned i = 0; i < m_precision; i++, j++) {
        b[i] = 0;
        b[j] = s[i];
    }
}

void mpff_manager::del(mpff & n) {
    unsigned sig_idx = n.m_sig_idx;
    if (sig_idx != 0) {
        m_id_gen.recycle(sig_idx);
        unsigned * s = sig(n);
        for (unsigned i = 0; i < m_precision; i++)
            s[i] = 0;
    }
}

void mpff_manager::reset(mpff & n) {
    del(n);
    n.m_sign     = false;
    n.m_sig_idx  = 0;
    n.m_exponent = 0;
    SASSERT(check(n));
}

bool mpff_manager::is_int(mpff const & n) const {
    if (n.m_exponent >= 0) 
        return true; // cheap case
    if (n.m_exponent <= -static_cast<int>(m_precision_bits))
        return false; 
    return !has_one_at_first_k_bits(m_precision, sig(n), -n.m_exponent);
}

bool mpff_manager::is_int64(mpff const & n) const {
    SASSERT(m_precision >= 2);
    if (is_zero(n))
        return true;
    int max_exp = -static_cast<int>(sizeof(unsigned) * 8 * (m_precision - 2));
    if (n.m_exponent < max_exp) {
        return n.m_exponent > -static_cast<int>(m_precision_bits) &&
            !has_one_at_first_k_bits(m_precision, sig(n), -n.m_exponent);
    }
    else if (n.m_exponent == max_exp) {
        // handle INT64_MIN case
        unsigned * s = sig(n);
        return is_neg(n) && s[m_precision-1] == 0x80000000u && ::is_zero(m_precision-1, s);
    }
    else {
        return false;
    }
}

bool mpff_manager::is_uint64(mpff const & n) const {
    SASSERT(m_precision >= 2);
    if (is_zero(n))
        return true;
    return 
        n.m_sign == 0 &&
        n.m_exponent <= -static_cast<int>(sizeof(unsigned) * 8 * (m_precision - 2)) &&
        n.m_exponent > -static_cast<int>(m_precision_bits) &&               
        !has_one_at_first_k_bits(m_precision, sig(n), -n.m_exponent);                       
}

uint64_t mpff_manager::get_uint64(mpff const & a) const {
    SASSERT(is_uint64(a));
    if (is_zero(a)) return 0;
    int exp = -a.m_exponent - sizeof(unsigned) * 8 * (m_precision - 2);
    SASSERT(exp >= 0);
    uint64_t * s = reinterpret_cast<uint64_t*>(sig(a) + (m_precision - 2));
    return *s >> exp;
}

int64_t mpff_manager::get_int64(mpff const & a) const {
    SASSERT(is_int64(a));
    if (is_zero(a)) return 0;
    int exp = -a.m_exponent - sizeof(unsigned) * 8 * (m_precision - 2);
    SASSERT(exp >= 0);
    uint64_t * s = reinterpret_cast<uint64_t*>(sig(a) + (m_precision - 2));
    // INT64_MIN case
    if (exp == 0 && *s == 0x8000000000000000ull && is_neg(a)) {
        return INT64_MIN;
    }
    else {
        int64_t r = *s >> exp;
        if (is_neg(a))
            r = -r;
        return r;
    }
}

// Return true if n is 1 or -1
bool mpff_manager::is_abs_one(mpff const & n) const {
    // That is, check whether
    //   n.exponent    == 1 - m_precision_bits
    //   n.significand == 0b10000...0  (that is, only the highest bit is set in the significand).
    if (n.m_exponent != 1 - static_cast<int>(m_precision_bits))
        return false; 
    unsigned * s = sig(n);
    if (s[m_precision - 1] != 0x80000000u)
        return false;
    for (unsigned i = 0; i < m_precision - 1; i++) 
        if (s[i] != 0)
            return false;
    return true;
}

bool mpff_manager::is_two(mpff const & n) const {
    // That is, check whether
    //   n.exponent    = 2 - m_precision_bits
    //   n.significand == 0b10000...0  (that is, only the highest bit is set in the significand).
    if (is_neg(n))
        return false;
    if (n.m_exponent != 2 - static_cast<int>(m_precision_bits))
        return false; 
    unsigned * s = sig(n);
    if (s[m_precision - 1] != 0x80000000u)
        return false;
    for (unsigned i = 0; i < m_precision - 1; i++) 
        if (s[i] != 0)
            return false;
    return true;
}

void mpff_manager::set(mpff & n, int v) {
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
    SASSERT(check(n));
}

void mpff_manager::set(mpff & n, unsigned v) {
    if (v == 0) {
        reset(n);
    }
    else {
        allocate_if_needed(n);
        n.m_sign              = 0;
        int num_leading_zeros = nlz_core(v);
        n.m_exponent          = static_cast<int>(8 * sizeof(unsigned)) - num_leading_zeros - static_cast<int>(m_precision_bits);
        v <<= num_leading_zeros;
        unsigned * s          = sig(n);
        s[m_precision - 1]    = v;
        for (unsigned i = 0; i < m_precision - 1; i++)
            s[i] = 0;
    }
    SASSERT(check(n));
}

void mpff_manager::set(mpff & n, int64_t v) {
    if (v == 0) {
        reset(n);
    }
    else {
        if (v < 0) {
            set(n, 1 + static_cast<uint64_t>(-(1+v)));
            n.m_sign = 1;
        }
        else {
            set(n, static_cast<uint64_t>(v));
        }
    }
    SASSERT(check(n));
    SASSERT(get_int64(n) == v);
}

void mpff_manager::set(mpff & n, uint64_t v) {
#ifdef Z3DEBUG
    uint64_t old_v = v;
#endif
    if (v == 0) {
        reset(n);
    }
    else {
        allocate_if_needed(n);
        n.m_sign              = 0;
        unsigned * _v         = reinterpret_cast<unsigned*>(&v);
        int num_leading_zeros = nlz(2, _v);
        n.m_exponent          = static_cast<int>(8 * sizeof(uint64_t)) - num_leading_zeros - static_cast<int>(m_precision_bits);
        v <<= num_leading_zeros;
        SASSERT(m_precision >= 2);
        unsigned * s          = sig(n);
        s[m_precision-1]      = _v[1];
        s[m_precision-2]      = _v[0];
        for (unsigned i = 0; i < m_precision - 2; i++)
            s[i] = 0;
    }
    SASSERT(check(n));
    SASSERT(get_uint64(n) == old_v);
}

void mpff_manager::set(mpff & n, int num, unsigned den) {
    scoped_mpff a(*this), b(*this);
    set(a, num);
    set(b, den);
    div(a, b, n);
    SASSERT(check(n));
}

void mpff_manager::set(mpff & n, int64_t num, uint64_t den) {
    scoped_mpff a(*this), b(*this);
    set(a, num);
    set(b, den);
    div(a, b, n);
    SASSERT(check(n));
}

void mpff_manager::set(mpff & n, mpff const & v) {
    if (is_zero(v)) {
        reset(n);
        return;
    }
    if (&n == &v)
        return;
    allocate_if_needed(n);
    n.m_sign     = v.m_sign;
    n.m_exponent = v.m_exponent;
    unsigned * s1 = sig(n);
    unsigned * s2 = sig(v);
    for (unsigned i = 0; i < m_precision; i++)
        s1[i] = s2[i];
    SASSERT(check(n));
}

template<bool SYNCH>
void mpff_manager::set_core(mpff & n, mpz_manager<SYNCH> & m, mpz const & v) {
    TRACE("mpff", tout << "mpz->mpff\n"; m.display(tout, v); tout << "\n";);
    if (m.is_int64(v)) {
        TRACE("mpff", tout << "is_int64 " << m.get_int64(v) << "\n";);
        set(n, m.get_int64(v));
    }
    else if (m.is_uint64(v)) {
        TRACE("mpff", tout << "is_uint64\n";);
        set(n, m.get_uint64(v));
    }
    else {
        allocate_if_needed(n);
        svector<unsigned> & w = m_set_buffer;
        n.m_sign = m.decompose(v, w);
        while (w.size() < m_precision) {
            w.push_back(0);
        }
        TRACE("mpff", tout << "w words: "; for (unsigned i = 0; i < w.size(); i++) tout << w[i] << " "; tout << "\n";);
        unsigned w_sz = w.size();
        SASSERT(w_sz >= m_precision);
        unsigned num_leading_zeros = nlz(w_sz, w.c_ptr());
        shl(w_sz, w.c_ptr(), num_leading_zeros, w_sz, w.c_ptr());
        unsigned * s = sig(n);
        unsigned i = m_precision;
        unsigned j = w_sz;
        while (i > 0) {
            --i;
            --j;
            s[i] = w[j];
        }
        n.m_exponent = j * 8 * sizeof(unsigned) - static_cast<int>(num_leading_zeros);
        if ((n.m_sign == 1) != m_to_plus_inf) {
            // must check whether it is precise or not
            while (j > 0) {
                --j;
                if (w[j] != 0) {
                    // imprecision detected.
                    inc_significand(n);
                }
            }
            // it is precise
        }
    }
    TRACE("mpff", tout << "mpz->mpff result:\n"; display_raw(tout, n); tout << "\n";);
    SASSERT(check(n));
}

void mpff_manager::set(mpff & n, unsynch_mpz_manager & m, mpz const & v) { 
    set_core(n, m, v); 
}

void mpff_manager::set(mpff & n, synch_mpz_manager & m, mpz const & v) { 
    set_core(n, m, v); 
}

template<bool SYNCH>
void mpff_manager::set_core(mpff & n, mpq_manager<SYNCH> & m, mpq const & v) {
    // TODO: improve precision?
    scoped_mpff num(*this), den(*this);
    set_core(num, m, v.numerator());
    {
        flet<bool> l(m_to_plus_inf, !m_to_plus_inf);
        set_core(den, m, v.denominator());
    }
    div(num, den, n);
    SASSERT(check(n));
}

void mpff_manager::set(mpff & n, unsynch_mpq_manager & m, mpq const & v) { 
    set_core(n, m, v); 
}

void mpff_manager::set(mpff & n, synch_mpq_manager & m, mpq const & v) { 
    set_core(n, m, v); 
}

bool mpff_manager::eq(mpff const & a, mpff const & b) const {
    if (is_zero(a) && is_zero(b))
        return true;
    if (is_zero(a) || is_zero(b))
        return false;
    if (a.m_sign     != b.m_sign || 
        a.m_exponent != b.m_exponent)
        return false;
    unsigned * s1 = sig(a);
    unsigned * s2 = sig(b);
    for (unsigned i = 0; i < m_precision; i++) 
        if (s1[i] != s2[i])
            return false;
    return true;
}

bool mpff_manager::lt(mpff const & a, mpff const & b) const {
    STRACE("mpff_trace", tout << "[mpff] ("; display(tout, a); tout << " < "; display(tout, b); tout << ") == ";);
    if (is_zero(a)) {
        if (is_zero(b) || is_neg(b)) {
            STRACE("mpff_trace", tout << "(1 == 0)\n";);
            return false;
        }
        else {
            STRACE("mpff_trace", tout << "(1 == 1)\n";);
            SASSERT(is_pos(b));
            return true;
        }
    }
    if (is_zero(b)) {
        SASSERT(!is_zero(a));
        if (is_neg(a)) {
            STRACE("mpff_trace", tout << "(1 == 1)\n";);
            return true;
        }
        else {
            SASSERT(is_pos(a));
            STRACE("mpff_trace", tout << "(1 == 0)\n";);
            return false;
        }
    }
    SASSERT(!is_zero(a));
    SASSERT(!is_zero(b));
    if (a.m_sign == 1) {
        if (b.m_sign == 0) {
            STRACE("mpff_trace", tout << "(1 == 1)\n";);
            return true; // neg < pos
        }
        // case: neg neg 
        bool r = 
            b.m_exponent < a.m_exponent || 
            (a.m_exponent == b.m_exponent && ::lt(m_precision, sig(b), sig(a)));
        STRACE("mpff_trace", tout << "(" << r << " == 1)\n";);
        return r;
    }
    else {
        if (b.m_sign == 1) {
            STRACE("mpff_trace", tout << "(1 == 0)\n";);
            return false; // pos < neg
        }
        // case: pos pos
        bool r =
            a.m_exponent < b.m_exponent ||
            (a.m_exponent == b.m_exponent && ::lt(m_precision, sig(a), sig(b)));
        STRACE("mpff_trace", tout << "(" << r << " == 1)\n";);
        return r;
    }
}

void mpff_manager::inc_significand(unsigned * s, int64_t & exp) {
    if (!::inc(m_precision, s)) {
        SASSERT(::is_zero(m_precision, s));
        s[m_precision - 1] = MIN_MSW;
        SASSERT(exp != INT64_MAX);
        exp++;
    }
}

void mpff_manager::inc_significand(mpff & a) {
    unsigned * s = sig(a);
    if (!::inc(m_precision, s)) {
        // Overflow happened, a was of the form 0xFFFF...FF
        // Now, it must be 0x000...000 
        SASSERT(::is_zero(m_precision, s));
        // Set it to 0x80000...000, and increment exponent by 1.
        s[m_precision - 1] = MIN_MSW;
        if (a.m_exponent == INT_MAX)
            throw overflow_exception();
        a.m_exponent++;
    }
}

void mpff_manager::dec_significand(mpff & a) {
    SASSERT(!is_minus_epsilon(a) && !is_zero(a) && !is_plus_epsilon(a));
    unsigned * s = sig(a);
    for (unsigned i = 0; i < m_precision - 1; i++) {
        s[i]--;
        if (s[i] != UINT_MAX)
            return;
    }
    s[m_precision - 1]--;
    if (s[m_precision - 1] < MIN_MSW) {
        s[m_precision - 1] = UINT_MAX;
        a.m_exponent--;
    }
}

bool mpff_manager::min_significand(mpff const & a) const {
    unsigned * s = sig(a);
    return s[m_precision - 1] == MIN_MSW && ::is_zero(m_precision - 1, s);
}

bool mpff_manager::is_minus_epsilon(mpff const & a) const {
    return a.m_sign == 1 && a.m_exponent == INT_MIN && min_significand(a);
}

bool mpff_manager::is_plus_epsilon(mpff const & a) const {
    return a.m_sign == 0 && a.m_exponent == INT_MIN && min_significand(a);
}

void mpff_manager::set_min_significand(mpff & a) {
    // Since the most significand bit of the most significand word must be 1 in our representation,
    // we have that 0x8000..00 is the minimal significand
    unsigned * s = sig(a);
    s[m_precision - 1] = MIN_MSW;
    for (unsigned i = 0; i < m_precision - 1; i++) 
        s[i] = 0;
}

void mpff_manager::set_max_significand(mpff & a) {
    SASSERT(!is_zero(a));
    unsigned * s = sig(a);
    for (unsigned i = 0; i < m_precision; i++) 
        s[i] = UINT_MAX;
}

void mpff_manager::set_plus_epsilon(mpff & n) {
    allocate_if_needed(n);
    n.m_sign     = 0;
    n.m_exponent = INT_MIN;
    set_min_significand(n);
    SASSERT(check(n));
}

void mpff_manager::set_minus_epsilon(mpff & n) {
    set_plus_epsilon(n);
    n.m_sign = 1;
    SASSERT(check(n));
}

void mpff_manager::set_max(mpff & n) {
    allocate_if_needed(n);
    n.m_sign     = 0;
    n.m_exponent = INT_MAX;
    set_max_significand(n);
    SASSERT(check(n));
}

void mpff_manager::set_min(mpff & n) {
    set_max(n);
    n.m_sign = 1;
    SASSERT(check(n));
}

void mpff_manager::next(mpff & a) {
    if (is_zero(a)) {
        set_plus_epsilon(a);
    }
    else if (is_minus_epsilon(a)) {
        reset(a);
    }
    else if (a.m_sign == 0) {
        inc_significand(a);
    }
    else {
        dec_significand(a);
    }
    SASSERT(check(a));
}

void mpff_manager::prev(mpff & a) {
    if (is_zero(a)) {
        set_minus_epsilon(a);
    }
    else if (is_plus_epsilon(a)) {
        reset(a);
    }
    else if (a.m_sign == 0) {
        dec_significand(a);
    }
    else {
        inc_significand(a);
    }
    SASSERT(check(a));
}

void mpff_manager::set_big_exponent(mpff & a, int64_t e) {
    SASSERT(e > INT_MAX || e < INT_MIN);
    if (e > INT_MAX) {
        if (a.m_sign == 1) {
            if (m_to_plus_inf)
                set_min(a);
            else
                throw overflow_exception();
        }
        else {
            if (m_to_plus_inf)
                throw overflow_exception();
            else
                set_max(a);
        }
    }
    else {
        SASSERT(e < INT_MIN);
        if (a.m_sign == 1) {
            if (m_to_plus_inf)
                reset(a);
            else
                set_minus_epsilon(a);
        }
        else {
            if (m_to_plus_inf)
                set_plus_epsilon(a);
            else
                reset(a);
        }
    }
}

void mpff_manager::add_sub(bool is_sub, mpff const & a, mpff const & b, mpff & c) {
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

    TRACE("mpff", tout << (is_sub ? "sub" : "add") << "("; display(tout, a); tout << ", "; display(tout, b); tout << ")\n";);
    
    // Remark: any result returned by sig(...) may be invalid after a call to allocate_if_needed()
    // So, we must invoke allocate_if_needed(c) before we invoke sig(a) and sig(b).
    allocate_if_needed(c); 
    
    bool       sgn_a, sgn_b;
    int        exp_a, exp_b;
    unsigned * sig_a, * sig_b;

    if (a.m_exponent >= b.m_exponent) {
        sgn_a = a.m_sign != 0;
        sgn_b = b.m_sign != 0;
        exp_a = a.m_exponent;
        exp_b = b.m_exponent;
        sig_a = sig(a);
        sig_b = sig(b);
        if (is_sub)
            sgn_b = !sgn_b;
    }
    else {
        sgn_a = b.m_sign != 0;
        sgn_b = a.m_sign != 0;
        exp_a = b.m_exponent;
        exp_b = a.m_exponent;
        sig_a = sig(b);
        sig_b = sig(a);
        if (is_sub)
            sgn_a = !sgn_a;
    }
    
    SASSERT(exp_a >= exp_b);

    unsigned * n_sig_b; // normalized sig_b
    
    // Make sure that a and b have the same exponent.
    if (exp_a > exp_b) {
        unsigned shift = (unsigned)exp_a - (unsigned)exp_b;
        n_sig_b = m_buffers[0].c_ptr();
        shr(m_precision, sig_b, shift, m_precision, n_sig_b);
        if (sgn_b != m_to_plus_inf && has_one_at_first_k_bits(m_precision, sig_b, shift)) {
            // Precision was lost when normalizing the significand.
            // The current rounding mode forces us to bump the significand.
            // Remark: an overflow cannot happen when incrementing the significand.
            VERIFY(::inc(m_precision, n_sig_b));
        }
    }
    else {
        SASSERT(exp_a == exp_b);
        n_sig_b = sig_b;
    }

    // Compute c
    if (sgn_a == sgn_b) {
        c.m_sign = sgn_a;
        unsigned * sig_r = m_buffers[1].c_ptr();
        size_t   r_sz;
        m_mpn_manager.add(sig_a, m_precision, n_sig_b, m_precision, sig_r, m_precision + 1, &r_sz);
        SASSERT(r_sz <= m_precision + 1);
        unsigned num_leading_zeros = nlz(m_precision + 1, sig_r);
        SASSERT(num_leading_zeros >= sizeof(unsigned) * 8 - 1); // num_leading_zeros >= 31
        SASSERT(num_leading_zeros <  sizeof(unsigned) * 8 * (m_precision + 1)); // result is not zero.
        unsigned * sig_c = sig(c);
        if (num_leading_zeros == sizeof(unsigned) * 8) {
            // no shift is needed
            c.m_exponent = exp_a;
            for (unsigned i = 0; i < m_precision; i++)
                sig_c[i] = sig_r[i];
        }
        else if (num_leading_zeros == sizeof(unsigned) * 8 - 1) {
            // shift 1 right
            bool _inc_significand = ((c.m_sign == 1) != m_to_plus_inf) && has_one_at_first_k_bits(m_precision*2, sig_r, 1);
            int64_t exp_c = exp_a;
            exp_c++;
            shr(m_precision + 1, sig_r, 1, m_precision, sig_c);
            if (_inc_significand)
                inc_significand(sig_c, exp_c);
            set_exponent(c, exp_c);
        }
        else {
            SASSERT(num_leading_zeros > sizeof(unsigned) * 8);
            num_leading_zeros -= sizeof(unsigned) * 8; // remove 1 word bits.
            // Now, we can assume sig_r has size m_precision 
            SASSERT(num_leading_zeros > 0);
            // shift left num_leading_zeros
            int64_t exp_c = exp_a;
            exp_c -= num_leading_zeros;
            shl(m_precision, sig_r, num_leading_zeros, m_precision, sig_c);
            set_exponent(c, exp_c);
        }
    }
    else {
        unsigned borrow;
        SASSERT(sgn_a != sgn_b);
        unsigned * sig_c = sig(c);
        if (::lt(m_precision, sig_a, n_sig_b)) {
            c.m_sign = sgn_b;
            m_mpn_manager.sub(n_sig_b, m_precision, sig_a, m_precision, sig_c, &borrow);
        }
        else {
            c.m_sign = sgn_a;
            m_mpn_manager.sub(sig_a, m_precision, n_sig_b, m_precision, sig_c, &borrow);
        }
        SASSERT(borrow == 0);
        unsigned num_leading_zeros = nlz(m_precision, sig_c);
        if (num_leading_zeros == m_precision_bits) {
            reset(c);
        }
        else if (num_leading_zeros > 0) {
            int64_t exp_c = exp_a;
            exp_c -= num_leading_zeros;
            shl(m_precision, sig_c, num_leading_zeros, m_precision, sig_c);
            set_exponent(c, exp_c);
        }
        else {
            SASSERT(num_leading_zeros == 0);
            c.m_exponent = exp_a;
        }
    }
    TRACE("mpff", tout << "result: "; display(tout, c); tout << "\n";);
    SASSERT(check(c));
}

void mpff_manager::add(mpff const & a, mpff const & b, mpff & c) {
    STRACE("mpff_trace", tout << "[mpff] "; display(tout, a); tout << " + "; display(tout, b); tout << " " << (m_to_plus_inf ? "<=" : ">=") << " ";);
    add_sub(false, a, b, c);
    STRACE("mpff_trace", display(tout, c); tout << "\n";);  
}

void mpff_manager::sub(mpff const & a, mpff const & b, mpff & c) {
    STRACE("mpff_trace", tout << "[mpff] "; display(tout, a); tout << " - "; display(tout, b); tout << " " << (m_to_plus_inf ? "<=" : ">=") << " ";);
    add_sub(true, a, b, c);
    STRACE("mpff_trace", display(tout, c); tout << "\n";);  
}

void mpff_manager::mul(mpff const & a, mpff const & b, mpff & c) {
    STRACE("mpff_trace", tout << "[mpff] ("; display(tout, a); tout << ") * ("; display(tout, b); tout << ") " << (m_to_plus_inf ? "<=" : ">=") << " ";);
    if (is_zero(a) || is_zero(b)) {
        reset(c);
    }
    else {
        allocate_if_needed(c);
        TRACE("mpff", tout << "mul("; display(tout, a); tout << ", "; display(tout, b); tout << ")\n";);
        c.m_sign    = a.m_sign ^ b.m_sign;
        // use int64_t to make sure we do not have overflows
        int64_t exp_a = a.m_exponent;
        int64_t exp_b = b.m_exponent;
        int64_t exp_c = exp_a + exp_b;
        // store result in m_buffers[0]
        unsigned * r = m_buffers[0].c_ptr();
        m_mpn_manager.mul(sig(a), m_precision, sig(b), m_precision, r);
        // r has 2*m_precision_bits bits
        unsigned num_leading_zeros = nlz(m_precision*2, r);
        SASSERT(num_leading_zeros <= m_precision_bits);
        TRACE("mpff", tout << "num_leading_zeros: " << num_leading_zeros << "\n";);
        // We must shift right (m_precision_bits - num_leading_zeros)
        // If r does not have a 1 bit in the first (m_precision_bits - num_leading_zeros), then the result is precise.
        unsigned shift = m_precision_bits - num_leading_zeros;
        // Imprecision == "lost digits"
        //    If c.m_sign  --> result became bigger   (e.g., -3.1 --> -3)
        //    If !c.m_sign --> result became smaller  (e.g., 3.1 --> 3)
        // Thus, when we are imprecise, we only need to bump the significand when:
        //    1) !c.m_sign &&  m_to_plus_inf   
        //    2)  c.m_sign && !m_to_plus_inf   
        bool _inc_significand = ((c.m_sign == 1) != m_to_plus_inf) && has_one_at_first_k_bits(m_precision*2, r, shift);
        TRACE("mpff", 
              tout << "c.m_sign: " << c.m_sign << ", m_to_plus_inf: " << m_to_plus_inf 
              << "\nhas_one_at_first_k_bits: " << has_one_at_first_k_bits(m_precision*2, r, shift) << "\n";
              tout << "_inc_significand: " << _inc_significand << "\n";);
        exp_c         += shift;
        unsigned * s_c = sig(c);
        shr(m_precision*2, r, shift, m_precision, s_c);
        if (_inc_significand)
            inc_significand(s_c, exp_c);
        set_exponent(c, exp_c);
        TRACE("mpff", tout << "result: "; display(tout, c); tout << "\n";);
        SASSERT(check(c));
    }
    STRACE("mpff_trace", display(tout, c); tout << "\n";);  
}

void mpff_manager::div(mpff const & a, mpff const & b, mpff & c) {
    if (is_zero(b)) 
        throw div0_exception();
    STRACE("mpff_trace", tout << "[mpff] ("; display(tout, a); tout << ") / ("; display(tout, b); tout << ") " << (m_to_plus_inf ? "<=" : ">=") << " ";);
    if (is_zero(a)) {
        reset(c);
    }
#if 1
    else if (is_two(b)) {
        set(c, a);
        int64_t exp_c = a.m_exponent;
        exp_c--;
        set_exponent(c, exp_c);
    }
#endif
    else {
        allocate_if_needed(c);
        c.m_sign    = a.m_sign ^ b.m_sign;
        // use int64_t to make sure we do not have overflows
        int64_t exp_a = a.m_exponent;
        int64_t exp_b = b.m_exponent;
        int64_t exp_c = exp_a - exp_b;
        
        exp_c      -= m_precision_bits; // we will multiplying (shifting) a by 2^m_precision_bits.
        // copy a to buffer 0, and shift by m_precision_bits
        to_buffer_shifting(0, a);
        unsigned * _a = m_buffers[0].c_ptr();
        unsigned * q  = m_buffers[1].c_ptr();
        unsigned q_sz = m_precision + 1;       // 2*m_precision - m_precision + 1
        unsigned * r  = m_buffers[2].c_ptr();
        unsigned r_sz = m_precision; 
        SASSERT(!::is_zero(2*m_precision, _a));
        SASSERT(!::is_zero(m_precision, sig(b)));
        SASSERT(nlz(2*m_precision, _a) == 0); 
        // Thus it is always the case that _a > b since size(a) = 2*size(b)
        // Actually, a is much bigger than b. 
        // b is at most  2^m_precision_bits - 1
        // a is at least 2^(2*m_precision_bits - 1)
        // Thus the quotient of a/b cannot be zero
        // Actually, quotient of a/b must be >= 2^(2*m_precision_bits - 1)/(2^m_precision_bits - 1)
        m_mpn_manager.div(_a, 2 * m_precision,
                          sig(b), m_precision,
                          q, 
                          r);
        TRACE("mpff_div", 
              unsigned j = q_sz; 
              while (j > 0) { --j; tout << std::hex << std::setfill('0') << std::setw(2*sizeof(unsigned)) << q[j]; tout << " "; } 
              tout << std::dec << "\n";);
        SASSERT(!::is_zero(q_sz, q));
        unsigned num_leading_zeros = nlz(q_sz, q);
        SASSERT(num_leading_zeros < q_sz * 8 * sizeof(unsigned));
        unsigned q_bits            = q_sz * 8 * sizeof(unsigned);
        SASSERT(num_leading_zeros < q_bits);
        unsigned actual_q_bits = q_bits - num_leading_zeros;
        bool _inc_significand;
        unsigned * s_c = sig(c);
        if (actual_q_bits > m_precision_bits) {
            unsigned shift = actual_q_bits - m_precision_bits;
            // We are imprecise if the remainder is != 0 or if we lost a bit when shifting.
            // See comment in mul(...)
            _inc_significand = 
                ((c.m_sign == 1) != m_to_plus_inf) && 
                (has_one_at_first_k_bits(q_sz, q, shift) || 
                 !::is_zero(r_sz, r));
            exp_c += shift;
            shr(q_sz, q, shift, m_precision, s_c);
        }
        else {
            // We are imprecise only if the remainder is != 0
            _inc_significand = 
                ((c.m_sign == 1) != m_to_plus_inf) && 
                !::is_zero(r_sz, r);
            if (actual_q_bits < m_precision_bits) {
                unsigned shift = m_precision_bits - actual_q_bits;
                exp_c -= shift;
                shl(q_sz, q, shift, m_precision, s_c);
            }
            else { 
                SASSERT(actual_q_bits == m_precision_bits);
                ::copy(q_sz, q, m_precision, s_c);
            }
        }
        if (_inc_significand)
            inc_significand(s_c, exp_c);
        set_exponent(c, exp_c);
        SASSERT(check(c));
    }
    STRACE("mpff_trace", display(tout, c); tout << "\n";);  
}

void mpff_manager::floor(mpff & n) {
    if (n.m_exponent >= 0)
        return; 
    STRACE("mpff_trace", tout << "[mpff] Floor["; display(tout, n); tout << "] == ";);
    if (n.m_exponent <= -static_cast<int>(m_precision_bits)) {
        // number is between (-1, 1)
        if (n.m_sign == 0)
            reset(n);
        else
            set(n, -1);
    }
    else {
        unsigned * s = sig(n);
        if (n.m_sign == 1 && has_one_at_first_k_bits(m_precision, s, -n.m_exponent)) {
            shr(m_precision, s, -n.m_exponent, m_precision, s);
            VERIFY(::inc(m_precision, s));
            int num_leading_zeros = nlz(m_precision, s);
            SASSERT(num_leading_zeros == -n.m_exponent || num_leading_zeros == -n.m_exponent - 1);
            if (num_leading_zeros != -n.m_exponent) {
                shl(m_precision, s, -n.m_exponent - 1, m_precision, s);
                n.m_exponent++;
            }
            else {
                shl(m_precision, s, -n.m_exponent, m_precision, s) ;
            }
        }
        else {
            // reset first n.m_exponent bits
            shr(m_precision, s, -n.m_exponent, m_precision, s);
            shl(m_precision, s, -n.m_exponent, m_precision, s);
        }
    }
    SASSERT(check(n));
    STRACE("mpff_trace", display(tout, n); tout << "\n";);  
}

void mpff_manager::ceil(mpff & n) {
    if (n.m_exponent >= 0)
        return; 
    STRACE("mpff_trace", tout << "[mpff] Ceiling["; display(tout, n); tout << "] == ";);
    if (n.m_exponent <= -static_cast<int>(m_precision_bits)) {
        // number is between (-1, 1)
        if (n.m_sign == 0)
            set(n, 1);
        else
            reset(n);
    }
    else {
        unsigned * s = sig(n);
        if (n.m_sign == 0 && has_one_at_first_k_bits(m_precision, s, -n.m_exponent)) {
            shr(m_precision, s, -n.m_exponent, m_precision, s);
            VERIFY(::inc(m_precision, s));
            int num_leading_zeros = nlz(m_precision, s);
            SASSERT(num_leading_zeros == -n.m_exponent || num_leading_zeros == -n.m_exponent - 1);
            if (num_leading_zeros != -n.m_exponent) {
                shl(m_precision, s, -n.m_exponent - 1, m_precision, s);
                n.m_exponent++;
            }
            else {
                shl(m_precision, s, -n.m_exponent, m_precision, s) ;
            }
        }
        else {
            // reset first n.m_exponent bits
            shr(m_precision, s, -n.m_exponent, m_precision, s);
            shl(m_precision, s, -n.m_exponent, m_precision, s);
        }
    }
    SASSERT(check(n));
    STRACE("mpff_trace", display(tout, n); tout << "\n";);  
}

void mpff_manager::power(mpff const & a, unsigned p, mpff & b) {
#ifdef _TRACE
    scoped_mpff _a(*this); _a = a;
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
        unsigned * s = sig(a);
        if (s[m_precision - 1] == 0x80000000u && ::is_zero(m_precision - 1, s)) {
            allocate_if_needed(b);
            if (p % 2 == 0)
                b.m_sign = 0;
            else
                b.m_sign = a.m_sign;
            int64_t exp = a.m_exponent;
            exp *= p;
            if (exp > INT_MAX || exp < INT_MIN)
                throw overflow_exception();
            exp += (m_precision_bits - 1)*(p - 1);
            if (exp > INT_MAX || exp < INT_MIN)
                throw overflow_exception();
            unsigned * r = sig(b);
            r[m_precision - 1] = 0x80000000u;
            for (unsigned i = 0; i < m_precision - 1; i++)
                r[i] = 0;
            b.m_exponent = static_cast<int>(exp);
        }
        else {
            unsigned mask = 1;
            scoped_mpff pw(*this);
            set(pw, a);
            set(b, 1);
            while (mask <= p) {
                if (mask & p)
                    mul(b, pw, b);
                mul(pw, pw, pw);
                mask = mask << 1;
            }
        }
    }
    STRACE("mpff_trace", tout << "[mpff] ("; display(tout, _a); tout << ") ^ " << _p << (m_to_plus_inf ? "<=" : ">="); display(tout, b); tout << "\n";);
    TRACE("mpff_power", display_raw(tout, b); tout << "\n";);
    SASSERT(check(b));
}

bool mpff_manager::is_power_of_two(mpff const & a, unsigned & k) const {
    if (!is_power_of_two(a))
        return false;
    int64_t exp = a.m_exponent + m_precision_bits - 1;
    SASSERT(exp >= 0);
    k = static_cast<unsigned>(exp);
    return true;
}

bool mpff_manager::is_power_of_two(mpff const & a) const {
    unsigned * s = sig(a);
    return is_pos(a) && a.m_exponent > -static_cast<int>(m_precision_bits) && s[m_precision - 1] == 0x80000000u && ::is_zero(m_precision - 1, s);
}

template<bool SYNCH>
void mpff_manager::significand_core(mpff const & n, mpz_manager<SYNCH> & m, mpz & t) {
    m.set(t, m_precision, sig(n));
}

void mpff_manager::significand(mpff const & n, unsynch_mpz_manager & m, mpz & t) {
    significand_core(n, m, t);
}

void mpff_manager::significand(mpff const & n, synch_mpz_manager & m, mpz & t) {
    significand_core(n, m, t);
}

template<bool SYNCH>
void mpff_manager::to_mpz_core(mpff const & n, mpz_manager<SYNCH> & m, mpz & t) {
    SASSERT(is_int(n));
    int exp = n.m_exponent;
    if (exp < 0) {
        SASSERT(exp > -static_cast<int>(m_precision_bits));
        to_buffer(0, n);
        unsigned * b = m_buffers[0].c_ptr();
        shr(m_precision, b, -exp, m_precision, b);
        m.set(t, m_precision, b);
    }
    else {
        m.set(t, m_precision, sig(n));
        if (exp > 0) {
            _scoped_numeral<mpz_manager<SYNCH> > p(m);
            m.set(p, 2);
            m.power(p, exp, p);
            m.mul(t, p, t);
        }
    }
    if (is_neg(n))
        m.neg(t);
} 

void mpff_manager::to_mpz(mpff const & n, unsynch_mpz_manager & m, mpz & t) {
    to_mpz_core(n, m, t);
}

void mpff_manager::to_mpz(mpff const & n, synch_mpz_manager & m, mpz & t) {
    to_mpz_core(n, m, t);
}

template<bool SYNCH>
void mpff_manager::to_mpq_core(mpff const & n, mpq_manager<SYNCH> & m, mpq & t) {
    int exp = n.m_exponent;
    TRACE("mpff_to_mpq", tout << "to_mpq: "; display(tout, n); tout << "\nexp: " << exp << "\n";);
    if (exp < 0 && exp > -static_cast<int>(m_precision_bits) && !has_one_at_first_k_bits(m_precision, sig(n), -n.m_exponent)) {
        to_buffer(0, n);
        unsigned * b = m_buffers[0].c_ptr();
        shr(m_precision, b, -exp, m_precision, b);
        m.set(t, m_precision, b);
    }
    else {
        m.set(t, m_precision, sig(n));
        if (exp != 0) {
            _scoped_numeral<mpq_manager<SYNCH> > p(m);
            m.set(p, 2);
            unsigned abs_exp;
            if (exp < 0) {
                // Avoid -INT_MIN == INT_MIN issue. It is not really useful, since we will run out of memory anyway.
                if (exp == INT_MIN)
                    abs_exp = static_cast<unsigned>(-static_cast<int64_t>(INT_MIN));
                else
                    abs_exp = -exp;
            }
            else {
                abs_exp = exp;
            }
            m.power(p, abs_exp, p);
            if (exp < 0)
                m.div(t, p, t);
            else
                m.mul(t, p, t);
        }
    }
    if (is_neg(n))
        m.neg(t);
} 

void mpff_manager::to_mpq(mpff const & n, unsynch_mpq_manager & m, mpq & t) {
    to_mpq_core(n, m, t);
}

void mpff_manager::to_mpq(mpff const & n, synch_mpq_manager & m, mpq & t) {
    to_mpq_core(n, m, t);
}

void mpff_manager::display_raw(std::ostream & out, mpff const & n) const {
    if (is_neg(n))
        out << "-";
    unsigned * s = sig(n);
    unsigned i   = m_precision;
    while(i > 0) {
        --i;
        out << std::hex << std::setfill('0') << std::setw(2 * sizeof(unsigned)) << s[i];
    }
    out << "*2^" << std::dec << n.m_exponent;
}

void mpff_manager::display(std::ostream & out, mpff const & n) const {
    if (is_neg(n))
        out << "-";
    to_buffer_ext(0, n);
    svector<unsigned> & u_buffer = const_cast<mpff_manager*>(this)->m_buffers[0];
    int num_trailing_zeros = ntz(m_precision, u_buffer.c_ptr());
    int shift = 0;
    int64_t exp = n.m_exponent; // use int64_t to avoid -INT_MIN == INT_MIN issue
    if (exp < 0) {
        if (num_trailing_zeros >= -exp) {
            shift = static_cast<int>(-exp);
            exp   = 0;
        }
        else {
            shift = num_trailing_zeros;
            exp  += num_trailing_zeros;
        }
    }
    if (shift > 0)
        shr(m_precision, u_buffer.c_ptr(), shift, u_buffer.c_ptr());
    sbuffer<char, 1024> str_buffer(11*m_precision, 0);
    out << m_mpn_manager.to_string(u_buffer.c_ptr(), m_precision, str_buffer.begin(), str_buffer.size());
    if (exp > 0) {
        if (exp <= 63) {
            uint64_t _exp = 1;
            _exp <<= exp;
            out << "*" << _exp;
        }
        else {
            out << "*2";
            if (exp > 1) {
                out << "^";
                out << exp;
            }
        }
    }
    else if (exp < 0) {
        exp = -exp;
        if (exp <= 63) {
            uint64_t _exp = 1;
            _exp <<= exp;
            out << "/" << _exp;
        }
        else {
            out << "/2";
            if (exp > 1) {
                out << "^";
                out << exp;
            }
        }
    }
}

void mpff_manager::display_decimal(std::ostream & out, mpff const & n, unsigned prec, unsigned min_exponent) {
    // The result in scientific notation when n.m_exponent >= min_exponent or n.m_exponent <= - min_exponent - m_precision_bits
    int64_t exp  = n.m_exponent;
    if (exp >= min_exponent || exp <= -static_cast<int64_t>(min_exponent) - m_precision_bits || is_int(n)) {
        display(out, n);
        return;
    }
    if (is_neg(n))
        out << "-";
    unsigned word_sz = 8 * sizeof(unsigned);
    if (exp >= 0) {
        sbuffer<unsigned, 1024> buffer;
        unsigned num_extra_words = 1 + static_cast<unsigned>(exp/word_sz);
        unsigned shift           = word_sz - exp%word_sz;
        for (unsigned i = 0; i < num_extra_words; i++)
            buffer.push_back(0);
        unsigned * s = sig(n);
        for (unsigned i = 0; i < m_precision; i++) 
            buffer.push_back(s[i]);
        shr(buffer.size(), buffer.c_ptr(), shift, buffer.size(), buffer.c_ptr());
        sbuffer<char, 1024> str_buffer(11*buffer.size(), 0);
        out << m_mpn_manager.to_string(buffer.c_ptr(), buffer.size(), str_buffer.begin(), str_buffer.size());
    }
    else {
        sbuffer<unsigned, 1024> buffer1, buffer2;
        sbuffer<unsigned> buffer3;
        exp = -exp;
        unsigned num_words       = 1 + static_cast<unsigned>(exp/word_sz);
        unsigned num_extra_words = m_precision < num_words ? num_words - m_precision : 0;
        num_extra_words++;
        unsigned * s = sig(n);
        for (unsigned i = 0; i < m_precision; i++)  {
            buffer1.push_back(s[i]);
            buffer2.push_back(0);
            buffer3.push_back(0);
        }
        for (unsigned i = 0; i < num_extra_words; i++) {
            buffer1.push_back(0);
            buffer2.push_back(0);
        }
        unsigned ten = 10;
        sbuffer<unsigned, 1024> pw_buffer;
        pw_buffer.resize(num_words, 0);
        pw_buffer[0] = 1;
        shl(num_words, pw_buffer.c_ptr(), static_cast<unsigned>(exp), num_words, pw_buffer.c_ptr());
        if (num_words > m_precision) {
            out << "0";
        }
        else {
            m_mpn_manager.div(buffer1.c_ptr(), m_precision,
                              pw_buffer.c_ptr(), num_words,
                              buffer3.c_ptr(),
                              buffer2.c_ptr());
            sbuffer<char, 1024> str_buffer(11*buffer3.size(), 0);
            out << m_mpn_manager.to_string(buffer3.c_ptr(), buffer3.size(), str_buffer.begin(), str_buffer.size());
            SASSERT(!::is_zero(buffer2.size(), buffer2.c_ptr())); // otherwise n is an integer
            ::copy(buffer2.size(), buffer2.c_ptr(), buffer1.size(), buffer1.c_ptr());
        }
        out << ".";        
        // buffer1 contain the fractional part
        unsigned i        = 0;
        unsigned sz1      = buffer1.size();
        while (sz1 > 0 && buffer1[sz1-1] == 0)
            --sz1;
        SASSERT(sz1 > 0); // otherwise the number is an integer
        while (sz1 > 0) {
            if (i >= prec) {
                out << "?";
                return;
            }
            i = i + 1;
            m_mpn_manager.mul(buffer1.c_ptr(), sz1, &ten, 1, buffer2.c_ptr());
            unsigned sz2 = sz1 + 1;
            while (sz2 > 0 && buffer2[sz2-1] == 0)
                --sz2;
            SASSERT(sz2 > 0);
            if (num_words > sz2) {
                out << "0";
                sz1 = sz2;
                ::copy(sz2, buffer2.c_ptr(), sz1, buffer1.c_ptr());
                SASSERT(sz1 == 0 || !::is_zero(sz1, buffer1.c_ptr()));
            }
            else {
                m_mpn_manager.div(buffer2.c_ptr(), sz2,
                                  pw_buffer.c_ptr(), num_words,
                                  buffer3.c_ptr(),
                                  buffer1.c_ptr());
                out << buffer3[0];
                sz1 = num_words;
                while (sz1 > 0 && buffer1[sz1-1] == 0)
                    --sz1;
                SASSERT(sz1 == 0 || !::is_zero(sz1, buffer1.c_ptr()));
            }
        }
    }
}

void mpff_manager::display_smt2(std::ostream & out, mpff const & n, bool decimal) const {
    if (is_neg(n))
        out << "(- ";
    to_buffer_ext(0, n);
    svector<unsigned> & u_buffer = const_cast<mpff_manager*>(this)->m_buffers[0];
    int num_trailing_zeros = ntz(m_precision, u_buffer.c_ptr());
    int shift = 0;
    int64_t exp = n.m_exponent;
    if (exp < 0) {
        if (num_trailing_zeros >= -exp) {
            shift = static_cast<int>(-exp);
            exp   = 0;
        }
        else {
            shift = num_trailing_zeros;
            exp  += num_trailing_zeros;
        }
    }
    if (shift > 0)
        shr(m_precision, u_buffer.c_ptr(), shift, u_buffer.c_ptr());

    if (exp > 0) 
        out << "(* ";
    else if (exp < 0)
        out << "(/ ";

    sbuffer<char, 1024> str_buffer(11*m_precision, 0);
    out << m_mpn_manager.to_string(u_buffer.c_ptr(), m_precision, str_buffer.begin(), str_buffer.size());
    if (decimal) out << ".0";

    if (exp != 0) {
        if (exp < 0) exp = -exp;
        if (exp <= 63) {
            uint64_t _exp = 1;
            _exp <<= exp;
            out << _exp;
            if (decimal) out << ".0";
        }
        else {
            out << " (^ 2"; 
            if (decimal) out << ".0";
            out << " " << exp;
            if (decimal) out << ".0";
            out << ")";
        }
        out << ")";
    }
    if (is_neg(n))
        out << ")";
}

std::string mpff_manager::to_string(mpff const & a) const {
    std::ostringstream buffer;
    display(buffer, a);
    return buffer.str();
}

std::string mpff_manager::to_rational_string(mpff const & a) const {
    // The exponent may be too big to encode without using 2^
    return to_string(a);
}

unsigned mpff_manager::prev_power_of_two(mpff const & a) {
    if (!is_pos(a))
        return 0;
    if (a.m_exponent <= -static_cast<int>(m_precision_bits))
        return 0; // Number is smaller than 1
    SASSERT(static_cast<int64_t>(a.m_exponent) + static_cast<int64_t>(m_precision_bits) - 1 >= 0);
    SASSERT(static_cast<int64_t>(a.m_exponent) + static_cast<int64_t>(m_precision_bits) - 1 <= static_cast<int64_t>(static_cast<uint64_t>(UINT_MAX)));
    return m_precision_bits + a.m_exponent - 1;
}

bool mpff_manager::check(mpff const & n) const {
    // n is zero or the most significand bit of the most significand word is 1.
    unsigned * s = sig(n);
    (void)s;
    SASSERT(is_zero(n) || (s[m_precision - 1] & MIN_MSW) != 0);
    // if n is zero, then the sign must be 0
    SASSERT(!is_zero(n) || n.m_sign == 0);
    // if n is zero, then all bits must be 0.
    SASSERT(!is_zero(n) || ::is_zero(m_precision, sig(n)));
    // if n is zero, then exponent must be 0.
    SASSERT(!is_zero(n) || n.m_exponent == 0);
    return true;
}
