/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    gmp_big_rational.h

Abstract:

    Big rationals using gmp

Author:

    Leonardo de Moura (leonardo) 2006-09-26.

Revision History:

--*/
#ifndef _GMP_BIG_RATIONAL_H_
#define _GMP_BIG_RATIONAL_H_

#ifndef NO_GMP

#include<string>
#include<gmp.h>
#include"util.h"
#include"debug.h"
#include"trace.h"

class big_rational {
    mpq_t        m_data;
    static mpz_t m_tmp;
    static bool  m_tmp_initialized;
    static mpz_t & get_tmp() { 
        if (!m_tmp_initialized) {
            mpz_init(m_tmp);
            m_tmp_initialized = true;
        }
        return m_tmp;
    }
    static mpz_t m_int_min;
    static mpz_t m_int_max;
    static mpz_t m_uint_max;
    static mpz_t m_two32;
    static mpz_t m_int64_min;
    static mpz_t m_int64_max;
    static mpz_t m_uint64_max;
    static bool  m_has_limits;
    static void init_limits();

    static mpz_t & int64_min() {
        if (!m_has_limits) {
            init_limits();
        }
        return m_int64_min;
    }

    static mpz_t & int64_max() {
        if (!m_has_limits) {
            init_limits();
        }
        return m_int64_max;
    }

    static mpz_t & uint64_max() {
        if (!m_has_limits) {
            init_limits();
        }
        return m_uint64_max;
    }
    
    static mpz_t & uint_max() {
        if (!m_has_limits) {
            init_limits();
        }
        return m_uint_max;
    }

    static mpz_t & two32() {
        if (!m_has_limits) {
            init_limits();
        }
        return m_two32;
    }
    
public:
    big_rational() { mpq_init(m_data); reset(); }
    big_rational(int n) { mpq_init(m_data); mpq_set_si(m_data, n, 1); }
    ~big_rational() { mpq_clear(m_data); }
    void reset() { mpq_set_si(m_data, 0, 1); }
    unsigned hash() const { return mpz_get_si(mpq_numref(m_data)); }
    void set(int num, int den) { 
        mpq_set_si(m_data, num, den);
        mpq_canonicalize(m_data);
    }
    void setu(unsigned num) {
        mpq_set_ui(m_data, num, 1);
        mpq_canonicalize(m_data);
    }
    void set(const char * str) {
        mpq_set_str(m_data, str, 10);
    }
    bool is_int() const {
        return mpz_cmp_ui(mpq_denref(m_data), 1) == 0;
    }
    bool is_even() const {
        if (!is_int()) {
            return false;
        }
        mpz_t & tmp = get_tmp();
        mpq_get_num(tmp, m_data);
        return mpz_even_p(tmp) != 0;
    }
    bool is_int64() const {
        if (!is_int()) {
            return false;
        }
        mpz_t & tmp = get_tmp();
        mpq_get_num(tmp, m_data);
        return mpz_fits_slong_p(tmp) || 
            (mpz_cmp(tmp, int64_min()) >= 0 && mpz_cmp(tmp, int64_max()) <= 0);
    }
    bool is_uint64() const {
        if (!is_int()) {
            return false;
        }
        mpz_t & tmp = get_tmp();
        mpq_get_num(tmp, m_data);
        return mpz_sgn(tmp) >= 0 && (mpz_fits_ulong_p(tmp) || mpz_cmp(tmp, uint64_max()) <= 0);
    }
    int64 get_int64() const;
    uint64 get_uint64() const;
    void neg() { mpq_neg(m_data, m_data); }
    big_rational & operator=(const big_rational & r) {
        mpq_set(m_data, r.m_data);
        return *this;
    }
    bool operator==(const big_rational & r) const { return mpq_equal(m_data, r.m_data) != 0; }
    bool operator<(const big_rational & r) const { return mpq_cmp(m_data, r.m_data) < 0; }
    big_rational & operator+=(const big_rational & r) {
        mpq_add(m_data, m_data, r.m_data);
        return *this;
    }
    big_rational & operator-=(const big_rational & r) {
        mpq_sub(m_data, m_data, r.m_data);
        return *this;
    }
    big_rational & operator*=(const big_rational & r) {
        mpq_mul(m_data, m_data, r.m_data);
        return *this;
    }
    big_rational & operator/=(const big_rational & r) {
        mpq_div(m_data, m_data, r.m_data);
        return *this;
    }
    big_rational & operator%=(const big_rational & r) {
        mpz_t & tmp = get_tmp();
        mpz_tdiv_r(tmp, mpq_numref(m_data), mpq_numref(r.m_data));
        mpq_set_z(m_data, tmp);
        return *this;
    }
    friend void div(const big_rational & r1, const big_rational & r2, big_rational & result) {
        mpz_t & tmp = get_tmp();
        mpz_tdiv_q(tmp, mpq_numref(r1.m_data), mpq_numref(r2.m_data));
        mpq_set_z(result.m_data, tmp);
    }
    void get_numerator(big_rational & result) {
        mpz_t & tmp = get_tmp();
        mpq_get_num(tmp, m_data);
        mpq_set_z(result.m_data, tmp);
    }
    void get_denominator(big_rational & result) {
        mpz_t & tmp = get_tmp();
        mpq_get_den(tmp, m_data);
        mpq_set_z(result.m_data, tmp);
    }
    void get_floor(big_rational & result) {
        mpz_t & tmp = get_tmp();
        mpz_fdiv_q(tmp, mpq_numref(m_data), mpq_denref(m_data));
        mpq_set_z(result.m_data, tmp);
    }
    std::string to_string() const;
#ifdef Z3DEBUG
    static void test() {
        init_limits();
    }
#endif
};

#endif 

#endif /* _GMP_BIG_RATIONAL_H_ */

