/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    mpzzp.h

Abstract:

    Combines Z ring, GF(p) finite field, and Z_p ring (when p is not a prime)
    in a single manager;

    That is, the manager may be dynamically configured
    to be Z Ring, GF(p), etc.

Author:

    Leonardo 2012-01-17.

Revision History:

    This code is based on mpzp.h.
    In the future, it will replace it.

--*/
#pragma once

#include "util/mpz.h"

class mpzzp_manager {
    typedef unsynch_mpz_manager numeral_manager;
    numeral_manager & m_manager;
    
    bool m_z;
    // instead the usual [0..p) we will keep the numbers in [lower, upper]
    mpz  m_p, m_lower, m_upper; 
    bool m_p_prime;
    mpz  m_inv_tmp1, m_inv_tmp2, m_inv_tmp3;
    mpz  m_div_tmp;

    bool is_p_normalized_core(mpz const & x) const {
        return m().ge(x, m_lower) && m().le(x, m_upper);
    }
    
    void setup_p() {
        SASSERT(m().is_pos(m_p) && !m().is_one(m_p));
        bool even = m().is_even(m_p);
        m().div(m_p, 2, m_upper); 
        m().set(m_lower, m_upper);
        m().neg(m_lower);
        if (even) {
            m().inc(m_lower);
        }
        TRACE("mpzzp", tout << "lower: " << m_manager.to_string(m_lower) << ", upper: " << m_manager.to_string(m_upper) << "\n";);
    }

    void p_normalize_core(mpz & x) {
        SASSERT(!m_z);
        m().rem(x, m_p, x); 
        if (m().gt(x, m_upper)) {
            m().sub(x, m_p, x);
        } else {
            if (m().lt(x, m_lower)) {
                m().add(x, m_p, x);
            }
        }
        SASSERT(is_p_normalized(x));
    }

public:
    typedef mpz numeral;
    static bool precise() { return true; }
    bool field() { return !m_z && m_p_prime; }
    bool finite() const { return !m_z; }
    bool modular() const { return !m_z; }

    mpzzp_manager(numeral_manager & _m):
        m_manager(_m), 
        m_z(true) {
    }
    
    mpzzp_manager(numeral_manager & _m, mpz const &  p, bool prime = true):
        m_manager(_m),
        m_z(false) {
        m().set(m_p, p);
        setup_p();
    }

    mpzzp_manager(numeral_manager & _m, uint64_t p, bool prime = true):
        m_manager(_m),
        m_z(false) {
        m().set(m_p, p);
        setup_p();
    }

    ~mpzzp_manager() {
        m().del(m_p);
        m().del(m_lower);
        m().del(m_upper);
        m().del(m_inv_tmp1);
        m().del(m_inv_tmp2);
        m().del(m_inv_tmp3);
        m().del(m_div_tmp);
    }

    bool is_p_normalized(mpz const & x) const {
        return m_z || is_p_normalized_core(x);
    }

    void p_normalize(mpz & x) {
        if (!m_z)
            p_normalize_core(x);
        SASSERT(is_p_normalized(x));
    }
    
    numeral_manager & m() const { return m_manager; }
    
    mpz const & p() const { return m_p; }

    void set_z() { m_z = true; }
    void set_zp(mpz const & new_p) { m_z = false; m_p_prime = true; m().set(m_p, new_p); setup_p(); }
    void set_zp(uint64_t new_p) { m_z = false; m_p_prime = true; m().set(m_p, new_p); setup_p(); }
    // p = p^2
    void set_p_sq() { SASSERT(!m_z); m_p_prime = false; m().mul(m_p, m_p, m_p); setup_p(); }
    void set_zp_swap(mpz & new_p) { SASSERT(!m_z); m().swap(m_p, new_p); setup_p(); }

    void reset(mpz & a) { m().reset(a); }
    bool is_small(mpz const & a) { return m().is_small(a); }
    void del(mpz & a) { m().del(a); }
    void neg(mpz & a) { m().neg(a); p_normalize(a); }    
    void abs(mpz & a) { m().abs(a); p_normalize(a); }
    bool is_zero(mpz const & a) { SASSERT(is_p_normalized(a)); return numeral_manager::is_zero(a); }
    bool is_one(mpz const & a) { SASSERT(is_p_normalized(a)); return numeral_manager::is_one(a); }
    bool is_pos(mpz const & a) { SASSERT(is_p_normalized(a)); return numeral_manager::is_pos(a); }
    bool is_neg(mpz const & a) { SASSERT(is_p_normalized(a)); return numeral_manager::is_neg(a); }
    bool is_nonpos(mpz const & a) { SASSERT(is_p_normalized(a)); return numeral_manager::is_nonpos(a); }
    bool is_nonneg(mpz const & a) { SASSERT(is_p_normalized(a)); return numeral_manager::is_nonneg(a); }
    bool is_minus_one(mpz const & a) { SASSERT(is_p_normalized(a)); return numeral_manager::is_minus_one(a); }    
    bool eq(mpz const & a, mpz const & b) { SASSERT(is_p_normalized(a) && is_p_normalized(b)); return m().eq(a, b); }
    bool lt(mpz const & a, mpz const & b) { SASSERT(is_p_normalized(a) && is_p_normalized(b)); return m().lt(a, b); }
    bool le(mpz const & a, mpz const & b) { SASSERT(is_p_normalized(a) && is_p_normalized(b)); return m().le(a, b); }
    bool gt(mpz const & a, mpz const & b) { SASSERT(is_p_normalized(a) && is_p_normalized(b)); return m().gt(a, b); }
    bool ge(mpz const & a, mpz const & b) { SASSERT(is_p_normalized(a) && is_p_normalized(b)); return m().ge(a, b); }
    std::string to_string(mpz const & a) const { 
        SASSERT(is_p_normalized(a));
        return m().to_string(a); 
    }
    void display(std::ostream & out, mpz const & a) const { m().display(out, a); }
    void add(mpz const & a, mpz const & b, mpz & c) { SASSERT(is_p_normalized(a) && is_p_normalized(b)); m().add(a, b, c); p_normalize(c); }
    void sub(mpz const & a, mpz const & b, mpz & c) { SASSERT(is_p_normalized(a) && is_p_normalized(b)); m().sub(a, b, c); p_normalize(c); }
    void inc(mpz & a) { SASSERT(is_p_normalized(a)); m().inc(a); p_normalize(a); }
    void dec(mpz & a) { SASSERT(is_p_normalized(a)); m().dec(a); p_normalize(a); }
    void mul(mpz const & a, mpz const & b, mpz & c) { SASSERT(is_p_normalized(a) && is_p_normalized(b)); m().mul(a, b, c); p_normalize(c); }
    void addmul(mpz const & a, mpz const & b, mpz const & c, mpz & d) { 
        SASSERT(is_p_normalized(a) && is_p_normalized(b) && is_p_normalized(c)); m().addmul(a, b, c, d); p_normalize(d); 
    }
    // d <- a - b*c
    void submul(mpz const & a, mpz const & b, mpz const & c, mpz & d) { 
        SASSERT(is_p_normalized(a));
        SASSERT(is_p_normalized(b));
        SASSERT(is_p_normalized(c)); 
        m().submul(a, b, c, d); 
        p_normalize(d); 
    }

    void inv(mpz & a) {
        if (m_z) {
            UNREACHABLE();
        }
        else {
            SASSERT(!is_zero(a));
            // eulers theorem a^(p - 2), but gcd could be more efficient 
            // a*t1 + p*t2 = 1 => a*t1 = 1 (mod p) => t1 is the inverse (t3 == 1)
            TRACE("mpzp_inv_bug", tout << "a: " << m().to_string(a) << ", p: " << m().to_string(m_p) << "\n";);
            p_normalize(a);
            TRACE("mpzp_inv_bug", tout << "after normalization a: " << m().to_string(a) << "\n";);
            m().gcd(a, m_p, m_inv_tmp1, m_inv_tmp2, m_inv_tmp3);
            TRACE("mpzp_inv_bug", tout << "tmp1: " << m().to_string(m_inv_tmp1) << "\ntmp2: " << m().to_string(m_inv_tmp2) 
                  << "\ntmp3: " << m().to_string(m_inv_tmp3) << "\n";);
            p_normalize(m_inv_tmp1);
            m().swap(a, m_inv_tmp1);
            SASSERT(m().is_one(m_inv_tmp3)); // otherwise p is not prime and inverse is not defined
        }
    }
    
    void swap(mpz & a, mpz & b) {
        SASSERT(is_p_normalized(a) && is_p_normalized(b));
        m().swap(a, b);
    }

    bool divides(mpz const & a, mpz const & b) { return (field() && !is_zero(a)) || m().divides(a, b); }

    // a/b = a*inv(b)
    void div(mpz const & a, mpz const & b, mpz & c) {
        if (m_z) {
            return m().div(a, b, c);
        }
        else {
            SASSERT(m_p_prime);
            SASSERT(is_p_normalized(a));
            m().set(m_div_tmp, b);
            inv(m_div_tmp);
            mul(a, m_div_tmp, c);
            SASSERT(is_p_normalized(c));
        }
    }
    
    static unsigned hash(mpz const & a) { return numeral_manager::hash(a); }

    void gcd(mpz const & a, mpz const & b, mpz & c) { 
        SASSERT(is_p_normalized(a) && is_p_normalized(b));
        m().gcd(a, b, c);
        SASSERT(is_p_normalized(c));
    }

    void gcd(unsigned sz, mpz const * as, mpz & g) {
        m().gcd(sz, as, g);
        SASSERT(is_p_normalized(g));
    }
    
    void gcd(mpz const & r1, mpz const & r2, mpz & a, mpz & b, mpz & g) { 
        SASSERT(is_p_normalized(r1) && is_p_normalized(r2));
        m().gcd(r1, r2, a, b, g);
        p_normalize(a);
        p_normalize(b);
    }

    void set(mpz & a, mpz & val) { m().set(a, val); p_normalize(a); }    
    void set(mpz & a, int val) { m().set(a, val); p_normalize(a); }    
    void set(mpz & a, unsigned val) { m().set(a, val); p_normalize(a); }
    void set(mpz & a, char const * val) { m().set(a, val); p_normalize(a); }
    void set(mpz & a, int64_t val) { m().set(a, val); p_normalize(a); }
    void set(mpz & a, uint64_t val) { m().set(a, val); p_normalize(a); }
    void set(mpz & a, mpz const & val) { m().set(a, val); p_normalize(a); }

    bool is_uint64(mpz & a) const { const_cast<mpzzp_manager*>(this)->p_normalize(a); return m().is_uint64(a); }
    bool is_int64(mpz & a) const { const_cast<mpzzp_manager*>(this)->p_normalize(a); return m().is_int64(a); }
    uint64_t get_uint64(mpz & a) const { const_cast<mpzzp_manager*>(this)->p_normalize(a); return m().get_uint64(a); }
    int64_t get_int64(mpz & a) const { const_cast<mpzzp_manager*>(this)->p_normalize(a); return m().get_int64(a); }
    double get_double(mpz & a) const { const_cast<mpzzp_manager*>(this)->p_normalize(a); return m().get_double(a); }
    void power(mpz const & a, unsigned k, mpz & b) { 
        SASSERT(is_p_normalized(a));
        unsigned mask = 1;
        mpz power;
        set(power, a);
        set(b, 1);
        while (mask <= k) {
            if (mask & k)
                mul(b, power, b);
            mul(power, power, power);
            mask = mask << 1;
        }
        del(power);
    }
    bool is_perfect_square(mpz const & a, mpz & root) { 
        if (m_z) {
            return m().is_perfect_square(a, root);
        }
        else {
            NOT_IMPLEMENTED_YET(); 
            return false; 
        }
    }

    bool is_uint64(mpz const & a) const { return m().is_uint64(a); }
    bool is_int64(mpz const & a) const { return m().is_int64(a); }
    uint64_t get_uint64(mpz const & a) const { return m().get_uint64(a); }
    int64_t get_int64(mpz const & a) const { return m().get_int64(a); }

    void mul2k(mpz & a, unsigned k) { m().mul2k(a, k); p_normalize(a); }
    void mul2k(mpz const & a, unsigned k, mpz & r) { m().mul2k(a, k, r); p_normalize(r); }
    unsigned power_of_two_multiple(mpz const & n) { return m().power_of_two_multiple(n); }
    unsigned log2(mpz const & n) { return m().log2(n); }
    unsigned mlog2(mpz const & n) { return m().mlog2(n); }
    void machine_div2k(mpz & a, unsigned k) { m().machine_div2k(a, k); SASSERT(is_p_normalized(a)); }
    void machine_div2k(mpz const & a, unsigned k, mpz & r) { m().machine_div2k(a, k, r); SASSERT(is_p_normalized(r)); }

    bool root(mpz & a, unsigned n) { SASSERT(!modular()); return m().root(a, n); }
    bool root(mpz const & a, unsigned n, mpz & r) { SASSERT(!modular()); return m().root(a, n, r); }

};


