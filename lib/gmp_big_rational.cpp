/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    gmp_big_rational.cpp

Abstract:

    Big rationals using GMP

Author:

    Leonardo de Moura (leonardo) 2006-09-26.

Revision History:

--*/
#include<limits.h>

#include"gmp_big_rational.h"
#include"trace.h"
#include"buffer.h"

#ifndef NO_GMP
mpz_t big_rational::m_tmp;
bool  big_rational::m_tmp_initialized = false;
mpz_t big_rational::m_int_min;
mpz_t big_rational::m_int_max;
mpz_t big_rational::m_uint_max;
mpz_t big_rational::m_two32;
mpz_t big_rational::m_int64_min;
mpz_t big_rational::m_int64_max;
mpz_t big_rational::m_uint64_max;
bool  big_rational::m_has_limits = false;

void big_rational::init_limits() {
    mpz_init(m_int_min);
    mpz_init(m_int_max);
    mpz_init(m_uint_max);
    mpz_init(m_two32);
    mpz_init(m_int64_min);
    mpz_init(m_int64_max);
    mpz_init(m_uint64_max);
    mpz_set_si(m_int_min,  INT_MIN);
    mpz_set_si(m_int_max,  INT_MAX);
    mpz_set_ui(m_uint_max, UINT_MAX);
    mpz_set_ui(m_two32, UINT_MAX);
    mpz_t & tmp = get_tmp();
    mpz_set_si(tmp, 1);
    mpz_add(m_two32, m_two32, tmp);
    unsigned max_l = static_cast<unsigned>(INT64_MAX % static_cast<int64>(UINT_MAX));
    unsigned max_h = static_cast<unsigned>(INT64_MAX / static_cast<int64>(UINT_MAX));
    mpz_set_ui(m_int64_max, max_h);
    mpz_mul(m_int64_max, m_uint_max, m_int64_max);
    mpz_set_ui(tmp, max_l);
    mpz_add(m_int64_max, tmp, m_int64_max);
    mpz_neg(m_int64_min, m_int64_max);
    mpz_set_si(tmp, -1);
    mpz_add(m_int64_min, m_int64_min, tmp);
    mpz_set(m_uint64_max, m_int64_max);
    mpz_set_si(tmp, 2);
    mpz_mul(m_uint64_max, m_uint64_max, tmp);
    mpz_set_si(tmp, 1);
    mpz_add(m_uint64_max, m_uint64_max, tmp);
    m_has_limits = true;
}

std::string big_rational::to_string() const {
    size_t sz = mpz_sizeinbase(mpq_numref(m_data), 10) + mpz_sizeinbase(mpq_numref(m_data), 10) + 3;
    buffer<char> b(sz, 0);
    mpq_get_str(b.c_ptr(), 10, m_data);
    std::string result(b.c_ptr());
    return result;
}

int64 big_rational::get_int64() const {
    if (!m_has_limits) {
        init_limits();
    }
    SASSERT(is_int64());
    mpz_t & tmp = get_tmp();
    mpq_get_num(tmp, m_data);
    if (sizeof(int64) == sizeof(long) || mpz_fits_slong_p(tmp)) {
        return mpz_get_si(tmp);
    }
    else {
        mpz_mod(tmp, tmp, two32());
        int64 r = static_cast<int64>(mpz_get_ui(tmp));
        mpq_get_num(tmp, m_data);
        mpz_div(tmp, tmp, two32());
        r += static_cast<int64>(mpz_get_si(tmp)) << static_cast<int64>(32);
        return r;
    }
}

uint64 big_rational::get_uint64() const {
    if (!m_has_limits) {
        init_limits();
    }
    SASSERT(is_uint64());
    mpz_t & tmp = get_tmp();
    mpq_get_num(tmp, m_data);
    if (sizeof(uint64) == sizeof(unsigned long) || mpz_fits_ulong_p(tmp)) {
        return mpz_get_ui(tmp);
    }
    else {
        mpz_mod(tmp, tmp, two32());
        uint64 r = static_cast<uint64>(mpz_get_ui(tmp));
        mpq_get_num(tmp, m_data);
        mpz_div(tmp, tmp, two32());
        r += static_cast<uint64>(mpz_get_ui(tmp)) << static_cast<uint64>(32);
        return r;
    }
}

#endif
