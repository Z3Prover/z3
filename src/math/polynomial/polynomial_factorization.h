/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    polynomial_factorization.h

Abstract:

    Methods for factoring polynomials.

Author:

    Dejan (t-dejanj) 2011-11-29

Notes:

   [1] Elwyn Ralph Berlekamp. Factoring Polynomials over Finite Fields. Bell System Technical Journal, 
       46(8-10):1853-1859, 1967.
   [2] Donald Ervin Knuth. The Art of Computer Programming, volume 2: Seminumerical Algorithms. Addison Wesley, third 
       edition, 1997.
   [3] Henri Cohen. A Course in Computational Algebraic Number Theory. Springer Verlag, 1993.

--*/

#pragma once

#if 0
// Disabled for reorg
#include "polynomial.h"
#include "upolynomial.h"
#include "bit_vector.h"
#include "z3_exception.h"

namespace polynomial {

    /**
       \brief Something to throw when we are in trouble.
    */
    class factorization_exception : public default_exception {
    public:
        factorization_exception(char const * msg) : default_exception(msg) {}
    };

    /**
       \brief Factor the polynomial f from Z[x1, ..., x_n]. Returns the index of the last factor that is completely
       factored. I.e., if the method returns m, then f_1, ..., f_m are true irreducible factors, and the rest might
       be further reducible.
    */
    unsigned factor(polynomial_ref & f, factors & factors);

    /**
       \brief Factor the square-free primitive polynomial f from Z[x1, ..., x_n]. Returns true if the factorization 
       was sucesseful, i.e. it was completed and the result is complete. Otherwise the quarantee is that the all but 
       the last factor are irreducible.
    */
    bool factor_square_free_primitive(polynomial_ref const & f, factors & factors);
}

inline std::ostream & operator<<(std::ostream & out, polynomial::factors & factors) {
    factors.display(out);
    return out;
}

#endif
