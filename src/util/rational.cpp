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
#include "util/mutex.h"
#include "util/util.h"
#include "util/rational.h"

synch_mpq_manager *  rational::g_mpq_manager = nullptr;
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

static DECLARE_MUTEX(g_powers_of_two);

rational rational::power_of_two(unsigned k) {
    rational result;
    lock_guard lock(*g_powers_of_two);
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
        ALLOC_MUTEX(g_powers_of_two);
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
    g_mpq_manager = nullptr;
    DEALLOC_MUTEX(g_powers_of_two);
}

bool rational::limit_denominator(rational &num, rational const& limit) {
    rational n, d;
    n = numerator(num);
    d = denominator(num);
    if (d < limit) return false;
    
    /*
      Iteratively computes approximation using continuous fraction
      decomposition
      
      p(-1) = 0, p(0) = 1
      p(j) = t(j)*p(j-1) + p(j-2)
      
      q(-1) = 1, q(0) = 0
      q(j) = t(j)*q(j-1) + q(j-2)
      
      cf[t1; t2, ..., tr] =  p(r) / q(r) for r >= 1
      reference: https://www.math.u-bordeaux.fr/~pjaming/M1/exposes/MA2.pdf
    */
    
    rational p0(0), p1(1);
    rational q0(1), q1(0);
    
    while (!d.is_zero()) {
        rational tj(0), rem(0);
        rational p2(0), q2(0);
        tj = div(n, d);
        
        q2 = tj * q1 + q0;
        p2 = tj * p1 + p0;
        if (q2 >= limit) {
            num = p2/q2;
            return true;
        }
        rem = n - tj * d;
        p0 = p1;
        p1 = p2;
        q0 = q1;
        q1 = q2;
        n = d;
        d = rem;
    }
    return false;
}

