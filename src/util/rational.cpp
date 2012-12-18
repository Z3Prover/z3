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
rational             rational::m_zero(0);
rational             rational::m_one(1);
rational             rational::m_minus_one(-1);
vector<rational>     rational::m_powers_of_two;

void mk_power_up_to(vector<rational> & pws, unsigned n) {
    if (pws.empty()) {
        pws.push_back(rational(1));
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

void rational::initialize() {
    if (!g_mpq_manager) {
        g_mpq_manager = alloc(synch_mpq_manager);
    }
}

void rational::finalize() {
    m_powers_of_two.finalize();
    dealloc(g_mpq_manager);
    g_mpq_manager = 0;
}

