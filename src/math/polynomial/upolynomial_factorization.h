/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    upolynomial_factorization.h

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
#ifndef UPOLYNOMIAL_FACTORIZATION_H_
#define UPOLYNOMIAL_FACTORIZATION_H_

#include "math/polynomial/upolynomial.h"
#include "math/polynomial/polynomial.h"
#include "util/bit_vector.h"
#include "util/z3_exception.h"

namespace upolynomial {
    typedef manager::scoped_numeral scoped_numeral;

    /**
       \brief Factor f into f = f_1^k_1 * ... * p_n^k_n, such that p_i are square-free and coprime.
    */
    void zp_square_free_factor(zp_manager & zp_upm, numeral_vector const & f, zp_factors & sq_free_factors);

    /**
       \brief Factor the monic square-free polynomial f from Z_p[x]. Returns true if factorization was successful, or false
       if f is an irreducible square-free polynomial in Z_p[x].
    */
    bool zp_factor_square_free(zp_manager & zp_upm, numeral_vector const & f, zp_factors & factors);

    inline bool zp_factor_square_free(zp_manager & zp_upm, numeral_vector const & f, zp_factors & factors, factor_params const & params) {
        return zp_factor_square_free(zp_upm, f, factors);
    }

    /**
       \brief Factor the monic square-free polynomial f from Z_p[x] using the Berlekamp algorithm. If randomized is true
       the factor splitting is done randomly [3], otherwise it is done as in the original Berlekamp [1].
    */
    bool zp_factor_square_free_berlekamp(zp_manager & zp_upm, numeral_vector const & f, zp_factors & factors, bool randomized = true);

    /**
       \brief Factor the polynomial f from Z_p[x]. Returns true if factorization was successful, or false if f is
       an irreducible polynomial in Z_p[x]
    */
    bool zp_factor(zp_manager & zp_upm, numeral_vector const & f, zp_factors & factors);

    /**
        \brief Performs a Hensel lift of A and B in Z_a to Z_b, where p is prime and a = p^{a_k}, b = p^{b_k},
        r = (a, b), with the following assumptions:
         * UA + VB = 1 (mod a) 
         * C = AB (mod b)
         * (l(A), r) = 1 (important in order to divide by A, i.e. to invert l(A))
        the output of is two polynomials A1, B1 (replacing A and B) such that A1 = A (mod b), B1 = B (mod b), 
        l(A1) = l(A), deg(A1) = deg(A), deg(B1) = deg(B) and C = A1 B1 (mod b*r). Such A1, B1 are unique if 
        r is prime. See [3] p. 138.

        The method will also change the zp_manager's module from b to b*r
    */
    void hensel_lift(z_manager & upm, numeral const & a, numeral const & b, numeral const & r,
        numeral_vector const & U, numeral_vector const & A, numeral_vector const & V, numeral_vector const & B,
        numeral_vector const & C, numeral_vector & A_lifted, numeral_vector & B_lifted);

    /**
       \brief Performs the Hensel lift for the (monic!) factors_p of f in Z_p to Z_{p^e}.
    */
    void hensel_lift(z_manager & upm, numeral_vector const & f, zp_factors const & factors_p, unsigned e, zp_factors & factors_pe);

    /**
       \brief Factor the square-free polynomial f from Z[x]. Returns true if factorization was successful, or false if
       f is an irreducible polynomial in Z[x]. The vector of factors is cleared.
    */
    bool factor_square_free(z_manager & upm, numeral_vector const & f, factors & fs, factor_params const & ps = factor_params());
    /**
       Similar to factor_square_free, but it is used to factor the k-th component f^k of a polynomial.
       That is, the factors of f are inserted as factors of degree k into fs.
    */
    bool factor_square_free(z_manager & upm, numeral_vector const & f, factors & fs, unsigned k, factor_params const & ps = factor_params());
};

#endif
