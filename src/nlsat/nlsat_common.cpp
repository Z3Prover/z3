/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    nlsat_common.cpp

Abstract:

    some common routines from nlsat

Author:

    Lev Nachmanson(levnach@hotmail.com) 2025-October.

Revision History:

--*/
#include "nlsat/nlsat_common.h"
namespace nlsat {
    /**
       \brief Wrapper for factorization
    */
    void factor(polynomial_ref & p, polynomial::cache& cache, polynomial_ref_vector & fs) {
        TRACE(nlsat_factor, tout << "factor\n" << p << "\n";);
        fs.reset();
        cache.factor(p.get(), fs);
    }
}
