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
#include"util.h"
#include"rational.h"
#ifdef _WINDOWS
#include<strsafe.h>
#endif

synch_mpq_manager *  rational::g_mpq_manager = 0;
rational             rational::m_zero;
rational             rational::m_one;
rational             rational::m_minus_one;
vector<rational>     rational::m_powers_of_two;

static void mk_power_up_to(vector<rational> & pws, unsigned n) {
    if (pws.empty()) {
        pws.push_back(rational::one());
    }
    unsigned sz = pws.size();
    rational curr = pws[sz - 1];
    rational two(2);
    for (unsigned i = sz; i <= n; i++) {
        curr *= two;
        pws.push_back(curr);
    }
}

rational rational::power_of_two(unsigned k) {
    rational result;
    #pragma omp critical (powers_of_two)
    {
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
        g_mpq_manager = alloc(synch_mpq_manager);
        m().set(m_zero.m_val, 0);
        m().set(m_one.m_val, 1);
        m().set(m_minus_one.m_val, -1);
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
    g_mpq_manager = 0;
}

