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
        // Use a todo list to iteratively factor polynomials until every
        // polynomial in fs is irreducible (cache.factor returns a single factor).
        // Start with the input polynomial on the queue.
        polynomial_ref_vector todo(fs.m());
        todo.push_back(p.get());
        for (unsigned idx = 0; idx < todo.size(); ++idx) {
            polynomial_ref_vector tmp(fs.m());
            polynomial_ref cur_ref(todo.get(idx), fs.m());
            cache.factor(cur_ref.get(), tmp);
            if (tmp.size() == 1) {
                // single factor -> consider it irreducible and add to output
                fs.push_back(tmp.get(0));
            }
            else {
                // Only multivariate factors are queued for further factoring.
                // Univariate factors are considered final and pushed directly to the output vector `fs`.
                for (unsigned i = 0; i < tmp.size(); ++i) {
                    if (polynomial::manager::is_univariate(tmp.get(i)))
                        fs.push_back(tmp.get(i));
                    else
                        todo.push_back(tmp.get(i));
                }
            }
        }
        TRACE(nlsat_factor, tout << fs.size() << " factors:\n";
         ::nlsat::display(tout, fs.m(), fs, polynomial::display_var_proc()) << "\n";
        );
    }
}
