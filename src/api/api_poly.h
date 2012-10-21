/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    api_poly.h

Abstract:
    External API for polynomial package
    
Author:

    Leonardo de Moura (leonardo) 2012-10-18.

Revision History:

--*/
#ifndef _API_POLY_H_
#define _API_POLY_H_

#include"polynomial.h"

struct _Z3_polynomial_manager {
    unsynch_mpz_manager m_num_manager;
    polynomial::manager m_manager;
    polynomial_ref      m_result;

    _Z3_polynomial_manager():
        m_manager(m_num_manager),
        m_result(m_manager) {
    }
};

inline _Z3_polynomial_manager * to_poly_manager(Z3_polynomial_manager m) { return reinterpret_cast<_Z3_polynomial_manager*>(m); }
inline Z3_polynomial_manager of_poly_manager(_Z3_polynomial_manager * m) { return reinterpret_cast<Z3_polynomial_manager>(m); }

inline polynomial::polynomial * to_poly(Z3_polynomial p) { return reinterpret_cast<polynomial::polynomial*>(p); }
inline Z3_polynomial of_poly(polynomial::polynomial * p) { return reinterpret_cast<Z3_polynomial>(p); }

#endif
