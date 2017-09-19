/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    polynomial_cache.h

Abstract:

    "Hash-consing" for polynomials

Author:

    Leonardo (leonardo) 2012-01-07

Notes:

--*/
#ifndef POLYNOMIAL_CACHE_H_
#define POLYNOMIAL_CACHE_H_

#include "math/polynomial/polynomial.h"

namespace polynomial {

    /**
       \brief Functor for creating unique polynomials and caching results of operations
    */
    class cache {
        struct imp;
        imp * m_imp;
    public:
        cache(manager & m);
        ~cache();
        manager & m() const;
        manager & pm() const { return m(); }
        polynomial * mk_unique(polynomial * p);
        void psc_chain(polynomial const * p, polynomial const * q, var x, polynomial_ref_vector & S);
        void factor(polynomial const * p, polynomial_ref_vector & distinct_factors);
        void reset();
    };
};

#endif
