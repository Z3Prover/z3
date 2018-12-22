/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    polynomial_factorization.cpp

Abstract:

    Implementation of polynomial factorization.

Author:

    Dejan (t-dejanj) 2011-11-15

Notes:

   [1] Elwyn Ralph Berlekamp. Factoring Polynomials over Finite Fields. Bell System Technical Journal, 
       46(8-10):1853-1859, 1967.
   [2] Donald Ervin Knuth. The Art of Computer Programming, volume 2: Seminumerical Algorithms. Addison Wesley, third 
       edition, 1997.
   [3] Henri Cohen. A Course in Computational Algebraic Number Theory. Springer Verlag, 1993.

--*/
#include "util/trace.h"
#include "util/util.h"
#include "math/polynomial/upolynomial_factorization_int.h"
#include "util/prime_generator.h"

using namespace std;

namespace upolynomial {

// get the prime as unsigned while throwing exceptions if anything goes bad`
unsigned get_p_from_manager(zp_numeral_manager const & zp_nm) {
    z_numeral_manager & nm = zp_nm.m();
    numeral const & p = zp_nm.p();
    if (!nm.is_uint64(p)) {
        throw upolynomial_exception("The prime number attempted in factorization is too big!");
    }
    uint64_t p_uint64 = nm.get_uint64(p);
    unsigned p_uint = static_cast<unsigned>(p_uint64);
    if (((uint64_t)p_uint) != p_uint64) {
        throw upolynomial_exception("The prime number attempted in factorization is too big!");
    }
    return p_uint;
}

/**
   \brief The Q-I matrix from Berelkamp's algorithm [1,2].
   
   Given a polynomial f = \sum f_k x^k of degree n, with f_i in Z_p[x], the i-th row of Q is a representation of 
   x^(p*i) modulo f, i.e.

      x^(p*i) modulo f = \sum_j q[i][j] x^j
    
   If f is of degree n, the matrix is square nxn. When the this matrix is constructed we obtain Q - I, because 
   this is what we need in the algorithm. After construction, the null space vectors can be extracted one-by one using 
   the next_null_space_vector method.
*/
class berlekamp_matrix {

    zp_manager &         m_upm;
    mpzzp_manager &      m_zpm;

    svector<mpz>         m_matrix;
    unsigned             m_size;

    unsigned             m_null_row;     // 0, ..., m_size - 1, state for null vectors
    svector<int>         m_column_pivot; // position of pivots in the columns
    svector<int>         m_row_pivot;    // position of pivots in the rows

    mpz & get(unsigned i, unsigned j) {
        SASSERT(i < m_size && j < m_size);
        return m_matrix[i*m_size + j];
    }

    mpz const & get(unsigned i, unsigned j) const {
        SASSERT(i < m_size && j < m_size);
        return m_matrix[i*m_size + j];
    }

public:
    
    /**
       \brief Construct the matrix as explained above, f should be in the Z_p.
    */
    berlekamp_matrix(zp_manager & upm, numeral_vector const & f)
    : m_upm(upm),
      m_zpm(upm.m()),
      m_size(m_upm.degree(f)),
      m_null_row(1),
      m_column_pivot(m_size, -1),
      m_row_pivot(m_size, -1) {
        unsigned p = get_p_from_manager(m_zpm);

        TRACE("polynomial::factorization::bughunt", tout << "polynomial::berlekamp_matrix("; m_upm.display(tout, f); tout << ", " << p << ")" << endl;);

        // the first row is always the vector [1, 0, ..., 0], since x^0 = 0 (modulo f)        
        m_matrix.push_back(1);
        for (unsigned j = 0; j < m_size; ++ j) {
            m_matrix.push_back(0);
        }

        // the rest of the rows, we can get as follows, given f = x^n + f_{n-1} x^{n-1} + ... + f_1 x + f_0
        // if x^k = \sum a_{k,j} x^j   (modulo p), hence 0 <= j <= n-1 then
        // x^{k+1} = a_{k,n-1}(-f_{n-1} x^{n-1} + ... + f_0) + a_{k,n-2} x^{n-1} + ... + a_{k, 0} x
        // so we can compute a_{k+1,j} = a_{k, j-1} - a_{k,n-1}*f_j
        // every p-th row we add to the matrix
        scoped_numeral tmp(m_zpm);
        unsigned row = 0, previous_row = 0;        
        for (unsigned k = 1; true; previous_row = row, ++ k) {

            // add another row if we need it
            if (k % p == 1) {
                if (++ row >= m_size) {
                    break;
                }                
                for (unsigned j = 0; j < m_size; ++ j) {
                    m_matrix.push_back(0);
                }            
            }            
            
            // the multiplier
            m_zpm.set(tmp, get(previous_row, m_size - 1));

            // go down the row and shift it
            for (unsigned j = m_size - 1; j > 0; -- j) {
                m_zpm.submul(get(previous_row, j-1), tmp, f[j], get(row, j));
            }

            // add the 0 element (same formula with a_{k,-1} = 0)
            m_zpm.mul(f[0], tmp, get(row, 0));
            m_zpm.neg(get(row, 0));
        }        

        // do Q - I
        for (unsigned i = 0; i < m_size; ++ i) {
            m_zpm.dec(get(i, i));
        }

        TRACE("polynomial::factorization::bughunt", tout << "polynomial::berlekamp_matrix():" << endl; display(tout); tout << endl;);
    }

    /**
       \brief Destructor, just removing the numbers
    */
    ~berlekamp_matrix() {
        for (unsigned k = 0; k < m_matrix.size(); ++ k) {
            m_zpm.del(m_matrix[k]);
        }
    }

    /**
       \brief 'Diagonalizes' the matrix using only column operations. The resulting matrix will have -1 at pivot
       elements. Returns the rank of the null space.
    */
    unsigned diagonalize() {
        
        scoped_numeral multiplier(m_zpm);

        unsigned null_rank = 0;
        for (unsigned i = 0; i < m_size; ++ i) {

            // get the first non-zero entry in the m_null_row row        
            bool column_found = false;
            for (unsigned j = 0; j < m_size; ++ j) {
                if (m_column_pivot[j] < 0 && !m_zpm.is_zero(get(i, j))) {                    
                    column_found = true;
                    m_column_pivot[j] = i;
                    m_row_pivot[i] = j;

                    // found a pivot, to make it -1 we compute the multiplier -p^-1
                    m_zpm.set(multiplier, get(i, j));
                    m_zpm.inv(multiplier);
                    m_zpm.neg(multiplier);

                    // multiply the pivot column with the multiplier
                    for (unsigned k = m_null_row; k < m_size; ++ k) {
                        m_zpm.mul(get(k, j), multiplier, get(k, j));                        
                    }
                    // pivot is -1 so we can add it to the rest of the columns to eliminate the row
                    for (unsigned other_j = 0; other_j < m_size; ++ other_j) {
                        if (j != other_j) {
                            m_zpm.set(multiplier, get(i, other_j));
                            for (unsigned k = m_null_row; k < m_size; ++ k) {
                                m_zpm.addmul(get(k, other_j), multiplier, get(k, j), get(k, other_j));
                            }
                        }
                    }
                }
            }
            if (!column_found) {
                null_rank ++;
            }
        }
    
        TRACE("polynomial::factorization::bughunt", tout << "polynomial::diagonalize():" << endl; display(tout); tout << endl;);
        
        return null_rank;
    }

    /**
       If rank of the matrix is n - r, we are interested in linearly independent vectors v_1, ..., v_r (the basis of
       the null space), such that v_k A = 0. This method will give one at a time. The method returns true if vector has
       been computed properly. The first vector [1, 0, ..., 0] is ignored (m_null_row starts from 1).       
    */
    bool next_null_space_vector(numeral_vector & v) {        
        SASSERT(v.size() <= m_size);
        v.resize(m_size);
        for (; m_null_row < m_size; ++ m_null_row) {
            if (m_row_pivot[m_null_row] < 0) {
                // output the vector
                for (unsigned j = 0; j < m_size; ++ j) {
                    if (m_row_pivot[j] >= 0) {
                        m_zpm.set(v[j], get(m_null_row, m_row_pivot[j]));
                    } 
                    else {
                        if (j == m_null_row) {
                            m_zpm.set(v[j], 1);
                        } 
                        else {
                            m_zpm.set(v[j], 0);
                        }
                    }
                }
                ++ m_null_row;
                return true;
            }
        }    
        // didn't find the vector
        return false;
    }

    /**
       \brief Display the matrix on the output stream.
    */
    void display(std::ostream & out) const {
        for (unsigned i = 0; i < m_matrix.size() / m_size; ++ i) {
            for (unsigned j = 0; j < m_size; ++ j) {
                out << m_zpm.to_string(get(i, j)) << "\t";    
            }
            out << endl;
        }
    }
};

/**
   See [3] p. 125.
*/
void zp_square_free_factor(zp_manager & upm, numeral_vector const & f, zp_factors & sq_free_factors) {

    zp_numeral_manager & nm = upm.m();
    unsigned p = get_p_from_manager(upm.m());

    TRACE("polynomial::factorization", tout << "polynomial::square_free_factor("; upm.display(tout, f); tout << ") over Z_" << p << endl;);    

    scoped_numeral_vector div_tmp(nm);

    // [initialize] T_0 = f, e = 1    
    // trim and get the make it monic if not already
    SASSERT(f.size() > 1);        
    scoped_numeral_vector T_0(nm);    
    upm.set(f.size(), f.c_ptr(), T_0);    
    scoped_numeral constant(nm);    
    upm.mk_monic(T_0.size(), T_0.c_ptr(), constant);
    sq_free_factors.set_constant(constant);
    TRACE("polynomial::factorization::bughunt", 
        tout << "Initial factors: " << sq_free_factors << endl;
        tout << "R.<x> = GF(" << p << ")['x']" << endl;
        tout << "T_0 = "; upm.display(tout, T_0); tout << endl;
    );    
    unsigned e = 1;

    // we repeat until we get a constant 
    scoped_numeral_vector T_0_d(nm);
    scoped_numeral_vector T(nm);        
    scoped_numeral_vector V(nm);
    scoped_numeral_vector W(nm);
    scoped_numeral_vector A_ek(nm);
    while (T_0.size() > 1) 
    {
        // [initialize e-loop] T = gcd(T_0, T_0'), V / T_0/T, k = 0
        unsigned k = 0;
        TRACE("polynomial::factorization::bughunt", tout << "k = 0" << endl;);    

        // T_0_d = T_0'
        upm.derivative(T_0.size(), T_0.c_ptr(), T_0_d);
        TRACE("polynomial::factorization::bughunt", 
            tout << "T_0_d = T_0.derivative(x)" << endl;    
            tout << "T_0_d == "; upm.display(tout, T_0_d); tout << endl;
        );    

        // T = gcd(T_0, T_0')
        upm.gcd(T_0.size(), T_0.c_ptr(), T_0_d.size(), T_0_d.c_ptr(), T);
        TRACE("polynomial::factorization::bughunt", 
            tout << "T = T_0.gcd(T_0_d)" << endl;
            tout << "T == "; upm.display(tout, T); tout << endl;
        );    

        // V = T_0 / T
        upm.div(T_0.size(), T_0.c_ptr(), T.size(), T.c_ptr(), V);
        TRACE("polynomial::factorization::bughunt", 
            tout << "V = T_0.quo_rem(T)[0]" << endl;
            tout << "V == "; upm.display(tout, V); tout << endl;
        );    

        while (V.size() > 1) {
            // [special case] 
            if ((++k) % p == 0) {
                ++ k;
                // T = T/V
                upm.div(T.size(), T.c_ptr(), V.size(), V.c_ptr(), T);
                TRACE("polynomial::factorization::bughunt", 
                    tout << "T = T.quo_rem(V)[0]" << endl;
                    tout << "T == "; upm.display(tout, T); tout << endl;
                );    
            }

            // [compute A_ek]

            // W = gcd(T, V)
            upm.gcd(T.size(), T.c_ptr(), V.size(), V.c_ptr(), W);
            TRACE("polynomial::factorization::bughunt", 
                tout << "W = T.gcd(V)" << endl;
                upm.display(tout, W); tout << endl;
            );    

            // A_ek = V/W
            upm.div(V.size(), V.c_ptr(), W.size(), W.c_ptr(), A_ek);
            TRACE("polynomial::factorization::bughunt", 
                tout << "A_ek = V.quo_rem(W)[0]" << endl;
                tout << "A_ek == "; upm.display(tout, A_ek); tout << endl;
            );    

            // V = W
            V.swap(W);
            TRACE("polynomial::factorization::bughunt", 
                tout << "V = W" << endl;    
                tout << "V == "; upm.display(tout, V); tout << endl;
            );    

            // T = T/V
            upm.div(T.size(), T.c_ptr(), V.size(), V.c_ptr(), T);
            TRACE("polynomial::factorization::bughunt", 
                tout << "T = T.quo_rem(V)[0]" << endl;
                tout << "T == "; upm.display(tout, T); tout << endl;
            );    

            // if not constant, we output it
            if (A_ek.size() > 1) {
                TRACE("polynomial::factorization::bughunt", tout << "Factor: ("; upm.display(tout, A_ek); tout << ")^" << e*k << endl;);    
                sq_free_factors.push_back(A_ek, e*k);
            }
        }

        // [finished e-loop] T_0 = \sum_{p div j} t_j x^j, set T_0 \sum_{p div j} t_j x^{j/p}, e = pe
        e *= p;
        T_0.reset();
        for (unsigned deg_p = 0; deg_p < T.size(); deg_p += p) {
            T_0.push_back(numeral());
            nm.set(T_0.back(), T[deg_p]);
        }
        TRACE("polynomial::factorization::bughunt", 
            tout << "T_0 = "; upm.display(tout, T_0); tout << endl;
        );    
    }

    TRACE("polynomial::factorization", tout << "polynomial::square_free_factor("; upm.display(tout, f); tout << ") => " << sq_free_factors << endl;);    
}

bool zp_factor(zp_manager & upm, numeral_vector const & f, zp_factors & factors) {


    TRACE("polynomial::factorization", 
          unsigned p = get_p_from_manager(upm.m());
          tout << "polynomial::factor("; upm.display(tout, f); tout << ") over Z_" << p << endl;);    

    // get the sq-free parts (all of them will be monic)
    zp_factors sq_free_factors(upm);
    zp_square_free_factor(upm, f, sq_free_factors);

    // factor the sq-free parts individually
    for (unsigned i = 0; i < sq_free_factors.distinct_factors(); ++ i) {
        unsigned j = factors.distinct_factors();
        if (upm.degree(sq_free_factors[i]) > 1) {
            zp_factor_square_free(upm, sq_free_factors[i], factors); // monic from aq-free decomposition
            for (; j < factors.distinct_factors(); ++ j) {
                factors.set_degree(j, sq_free_factors.get_degree(i)*factors.get_degree(j));
            }
        } 
        else {
            factors.push_back(sq_free_factors[i], sq_free_factors.get_degree(i));
        }
    }
    // add the constant
    factors.set_constant(sq_free_factors.get_constant());

    TRACE("polynomial::factorization", tout << "polynomial::factor("; upm.display(tout, f); tout << ") => " << factors << endl;);    

    return factors.total_factors() > 1;
}

bool zp_factor_square_free(zp_manager & upm, numeral_vector const & f, zp_factors & factors) {
    return zp_factor_square_free_berlekamp(upm, f, factors, false);
}

bool zp_factor_square_free_berlekamp(zp_manager & upm, numeral_vector const & f, zp_factors & factors, bool randomized) {    
    SASSERT(upm.degree(f) > 1);

    mpzzp_manager & zpm = upm.m();
    unsigned p = get_p_from_manager(zpm);
    
    TRACE("polynomial::factorization", tout << "upolynomial::factor_square_free_berlekamp("; upm.display(tout, f); tout << ", " << p << ")" << endl;);    
    SASSERT(zpm.is_one(f.back()));

    // construct the berlekamp Q matrix to get the null space
    berlekamp_matrix Q_I(upm, f);
    
    // copy the initial polynomial to factors
    unsigned first_factor = factors.distinct_factors();
    factors.push_back(f, 1);

    // rank of the null-space (and the number of factors)
    unsigned r = Q_I.diagonalize();
    if (r == 1) {
        // since r == 1 == number of factors, then f is irreducible
        TRACE("polynomial::factorization", tout << "upolynomial::factor_square_free_berlekamp("; upm.display(tout, f); tout << ", " << p << ") => " << factors << endl;);    
        return false;
    }

    TRACE("polynomial::factorization::bughunt", tout << "upolynomial::factor_square_free_berlekamp(): computing factors, expecting " << r << endl;);        

    scoped_numeral_vector gcd(zpm);
    scoped_numeral_vector div(zpm);

    // process the null space vectors (skip first one, it's [1, 0, ..., 0]) while generating the factors
    unsigned d = upm.degree(f);
    (void)d;
    scoped_numeral_vector v_k(zpm);
    while (Q_I.next_null_space_vector(v_k)) {

        TRACE("polynomial::factorization::bughunt", 
            tout << "null vector: "; 
            for(unsigned j = 0; j < d; ++ j) {
                tout << zpm.to_string(v_k[j]) << " ";
            }
            tout << endl;
        );
        
        upm.trim(v_k);
        // TRACE("polynomial::factorization", tout << "v_k = "; upm.display(tout, v_k); tout << endl;);    
        
        unsigned current_factor_end = factors.distinct_factors();
        for (unsigned current_factor_i = first_factor; current_factor_i < current_factor_end; ++ current_factor_i) {

            // we have v such that vQ = v, viewing v as a polynomial, we get that v^n - v = 0 (mod f)
            // since v^n -v = v*(v-1)*...*(v - p-1) we compute the gcd(v - s, f) to extract the 
            // factors. it also holds that g = \prod gcd(v - s, f), so we just accumulate them
            
            // if it's of degree 1, we're done (have to index the array as we are adding to it), as 
            if (factors[current_factor_i].size() == 2) {
                continue;
            }

            for (unsigned s = 0; s < p; ++ s) {
                
                numeral_vector const & current_factor = factors[current_factor_i];

                // we just take one off v_k each time to get all of them
                zpm.dec(v_k[0]);
            
                // get the gcd
                upm.gcd(v_k.size(), v_k.c_ptr(), current_factor.size(), current_factor.c_ptr(), gcd);

                // if the gcd is 1, or the gcd is f, we just ignore it
                if (gcd.size() != 1 && gcd.size() != current_factor.size()) {
                
                    // get the divisor also (no need to normalize the div, both are monic)
                    upm.div(current_factor.size(), current_factor.c_ptr(), gcd.size(), gcd.c_ptr(), div);

                    TRACE("polynomial::factorization::bughunt", 
                        tout << "current_factor = "; upm.display(tout, current_factor); tout << endl;
                        tout << "gcd_norm = "; upm.display(tout, gcd); tout << endl;
                        tout << "div = "; upm.display(tout, div); tout << endl;
                    );                

                    // continue with the rest
                    factors.swap_factor(current_factor_i, div);

                    // add the new factor(s)
                    factors.push_back(gcd, 1);

                } 

                // at the point where we have all the factors, we are done
                if (factors.distinct_factors() - first_factor == r) {
                    TRACE("polynomial::factorization", tout << "polynomial::factor("; upm.display(tout, f); tout << ", " << p << ") => " << factors << " of degree " << factors.get_degree() << endl;);    
                    return true;
                }
            }
        }
    }

    // should never get here
    SASSERT(false);
    return true;
}

/**
   Check if the hensel lifting was correct, i.e. that C = A*B (mod br).
*/
bool check_hansel_lift(z_manager & upm, numeral_vector const & C, 
    numeral const & a, numeral const & b, numeral const & r, 
    numeral_vector const & A, numeral_vector const & B,
    numeral_vector const & A_lifted, numeral_vector const & B_lifted) 
{
    z_numeral_manager & nm = upm.zm();

    scoped_mpz br(nm);
    nm.mul(b, r, br);
    
    zp_manager br_upm(upm.lim(), upm.zm());
    br_upm.set_zp(br);

    if (A_lifted.size() != A.size()) return false;
    if (B_lifted.size() != B.size()) return false;
    if (!nm.eq(A.back(), A_lifted.back())) return false;

    // test1: check that C = A_lifted * B_lifted (mod b*r)
    scoped_mpz_vector test1(nm);
    upm.mul(A_lifted.size(), A_lifted.c_ptr(), B_lifted.size(), B_lifted.c_ptr(), test1);
    upm.sub(C.size(), C.c_ptr(), test1.size(), test1.c_ptr(), test1);
    to_zp_manager(br_upm, test1);
    if (!test1.empty()) {
        TRACE("polynomial::factorization::bughunt", 
            tout << "sage: R.<x> = ZZ['x']" << endl;
            tout << "sage: A = "; upm.display(tout, A); tout << endl;
            tout << "sage: B = "; upm.display(tout, B); tout << endl;
            tout << "sage: C = "; upm.display(tout, C); tout << endl;
            tout << "sage: test1 = C - AB" << endl;
            tout << "sage: print test1.change_ring(GF(" << nm.to_string(br) << "))" << endl;
            tout << "sage: print 'expected 0'" << endl;
        );    
        return false;
    }

    zp_manager b_upm(upm.lim(), nm);
    b_upm.set_zp(b);

    // test2: A_lifted = A (mod b)
    scoped_mpz_vector test2a(nm), test2b(nm);
    to_zp_manager(b_upm, A, test2a);
    to_zp_manager(b_upm, A_lifted, test2b);
    if (!upm.eq(test2a, test2b)) {
        return false;
    }

    // test3: B_lifted = B (mod b)
    scoped_mpz_vector test3a(nm), test3b(nm);
    to_zp_manager(b_upm, B, test3a);
    to_zp_manager(b_upm, B_lifted, test3b);
    if (!upm.eq(test3a, test3b)) {
        return false;
    }

    return true;
}

/**
   Performs a Hensel lift of A and B in Z_a to Z_b, where p is prime and a = p^{a_k}, b = p^{b_k},
   r = (a, b), with the following assumptions:
   
     (1) UA + VB = 1 (mod a)
     (2) C = A*B (mod b)
     (3) (l(A), r) = 1 (important in order to divide by A, i.e. to invert l(A))
     (4) deg(A) + deg(B) = deg(C)

   The output of is two polynomials A1, B1  such that A1 = A (mod b), B1 = B (mod b), 
   l(A1) = l(A), deg(A1) = deg(A), deg(B1) = deg(B) and C = A1 B1 (mod b*r). Such A1, B1 are unique if 
   r is prime. See [3] p. 138.
*/
void hensel_lift(z_manager & upm, numeral const & a, numeral const & b, numeral const & r,
    numeral_vector const & U, numeral_vector const & A, numeral_vector const & V, numeral_vector const & B,
    numeral_vector const & C, numeral_vector & A_lifted, numeral_vector & B_lifted) {

    z_numeral_manager & nm = upm.zm();
    
    TRACE("polynomial::factorization::bughunt", 
        tout << "polynomial::hensel_lift(";
        tout << "a = " << nm.to_string(a) << ", ";
        tout << "b = " << nm.to_string(b) << ", ";
        tout << "r = " << nm.to_string(r) << ", ";
        tout << "U = "; upm.display(tout, U); tout << ", ";
        tout << "A = "; upm.display(tout, A); tout << ", ";
        tout << "V = "; upm.display(tout, V); tout << ", ";
        tout << "B = "; upm.display(tout, B); tout << ", ";
        tout << "C = "; upm.display(tout, C); tout << ")" << endl;
    );

    zp_manager r_upm(upm.lim(), nm);
    r_upm.set_zp(r);

    SASSERT(upm.degree(C) == upm.degree(A) + upm.degree(B));
    SASSERT(upm.degree(U) < upm.degree(B) && upm.degree(V) < upm.degree(A));

    // by (2) C = AB (mod b), hence (C - AB) is divisible by b
    // define thus let f = (C - AB)/b in Z_r
    scoped_numeral_vector f(upm.m());
    upm.mul(A.size(), A.c_ptr(), B.size(), B.c_ptr(), f); 
    upm.sub(C.size(), C.c_ptr(), f.size(), f.c_ptr(), f); 
    upm.div(f, b);
    to_zp_manager(r_upm, f);
    TRACE("polynomial::factorization", 
        tout << "f = "; upm.display(tout, f); tout << endl;
    );

    // we need to get A1 = A (mod b), B1 = B (mode b) so we know that we need 
    // A1 = A + b*S, B1 = B + b*T in Z[x] for some S and T with deg(S) <= deg(A), deg(T) <= deg(B)
    // we also need (mod b*r) C = A1*B1 = (A + b*S)*(B + b*T) = AB + b(AT + BS) + b^2*ST 
    // if we find S and T, we will have found our A1 and B1
    // since r divides b, then b^2 contains b*r and we know that it must be that C = AB + b(AT + BS) (mod b*r) 
    // which is equivalent to 
    //   (5) f = (C - AB)/b = AT + BS (mod r)     
    // having (1) AU + BV = 1 (mod r) and (5) AT + BS = f (mod r), we know that 
    // A*(fU) + B*(fV) = f (mod r), i.e. T = fU, S = fV is a solution
    // but we also know that we need an S with deg(S) <= deg(A) so we can do the following
    // we know that l(A) is invertible so we can find the exact remainder of fV with A, i.e. find the quotient
    // t in the division and set
    // A*(fU + tB) + B*(fV - tA) = f 
    // T = fU + tB, S = fU - tA
    // since l(A) is invertible in Z_r, we can (in Z_r) use exact division to get Vf = At + R with deg(R) < A
    // we now know that deg(A+bS) = deg(A), but we also know (4) which will guarantee that deg(B+bT) = deg(B)
    
    // compute the S, T (compute in Z_r[x])
    scoped_numeral_vector Vf(r_upm.m()), t(r_upm.m()), S(r_upm.m());
    TRACE("polynomial::factorization::bughunt", 
        tout << "V == "; upm.display(tout, V); tout << endl;
    );
    r_upm.mul(V.size(), V.c_ptr(), f.size(), f.c_ptr(), Vf);
    TRACE("polynomial::factorization::bughunt", 
        tout << "Vf = V*f" << endl; 
        tout << "Vf == "; upm.display(tout, Vf); tout << endl;
    );
    r_upm.div_rem(Vf.size(), Vf.c_ptr(), A.size(), A.c_ptr(), t, S);    
    TRACE("polynomial::factorization::bughunt", 
        tout << "[t, S] = Vf.quo_rem(A)" << endl; 
        tout << "t == "; upm.display(tout, t); tout << endl;
        tout << "S == "; upm.display(tout, S); tout << endl;
    );
    scoped_numeral_vector T(r_upm.m()), tmp(r_upm.m());
    r_upm.mul(U.size(), U.c_ptr(), f.size(), f.c_ptr(), T); // T = fU
    TRACE("polynomial::factorization::bughunt", 
        tout << "T == U*f" << endl; 
        tout << "T == "; upm.display(tout, T); tout << endl;
    );
    r_upm.mul(B.size(), B.c_ptr(), t.size(), t.c_ptr(), tmp); // tmp = Bt
    TRACE("polynomial::factorization::bughunt", 
        tout << "tmp = B*t" << endl; 
        tout << "tmp == "; upm.display(tout, tmp); tout << endl;
    );
    r_upm.add(T.size(), T.c_ptr(), tmp.size(), tmp.c_ptr(), T); // T = Uf + Bt
    TRACE("polynomial::factorization::bughunt", 
        tout << "T = B*tmp" << endl; 
        tout << "T == "; upm.display(tout, T); tout << endl;
    );

    // set the result, A1 = A + b*S, B1 = B + b*T (now we compute in Z[x])
    upm.mul(S, b);
    upm.mul(T, b);
    upm.add(A.size(), A.c_ptr(), S.size(), S.c_ptr(), A_lifted);
    upm.add(B.size(), B.c_ptr(), T.size(), T.c_ptr(), B_lifted);

    CASSERT("polynomial::factorizatio::bughunt", check_hansel_lift(upm, C, a, b, r, A, B, A_lifted, B_lifted));
}

bool check_quadratic_hensel(zp_manager & zpe_upm, numeral_vector const & U, numeral_vector const & A, numeral_vector const & V, numeral_vector const & B) {
    z_numeral_manager & nm = zpe_upm.zm();

    // compute UA+BV expecting to get 1 (in Z_pe[x])
    scoped_mpz_vector tmp1(nm);
    scoped_mpz_vector tmp2(nm);    
    zpe_upm.mul(U.size(), U.c_ptr(), A.size(), A.c_ptr(), tmp1);
    zpe_upm.mul(V.size(), V.c_ptr(), B.size(), B.c_ptr(), tmp2);
    scoped_mpz_vector one(nm);
    zpe_upm.add(tmp1.size(), tmp1.c_ptr(), tmp2.size(), tmp2.c_ptr(), one);
    if (one.size() != 1 || !nm.is_one(one[0])) {
        TRACE("polynomial::factorization::bughunt", 
            tout << "sage: R.<x> = Zmod(" << nm.to_string(zpe_upm.m().p()) << ")['x']" << endl;
            tout << "sage: A = "; zpe_upm.display(tout, A); tout << endl;
            tout << "sage: B = "; zpe_upm.display(tout, B); tout << endl;
            tout << "sage: U = "; zpe_upm.display(tout, U); tout << endl;
            tout << "sage: V = "; zpe_upm.display(tout, V); tout << endl;
            tout << "sage: print  (1 - UA - VB)" << endl;
            tout << "sage: print 'expected 0'" << endl;
        );    
        return false;
    }

    return true;
}

/**
   Lift C = A*B from Z_p[x] to Z_{p^e}[x] such that:
     * A = A_lift (mod p)
     * B = B_lift (mod p)
     * C = A*B (mod p^e)
*/
void hensel_lift_quadratic(z_manager& upm, numeral_vector const & C, 
                           zp_manager & zpe_upm, numeral_vector & A, numeral_vector & B, unsigned e) {
    z_numeral_manager & nm = upm.zm();

    TRACE("polynomial::factorization::bughunt", 
        tout << "polynomial::hansel_lift_quadratic(";
        tout << "A = "; upm.display(tout, A); tout << ", ";
        tout << "B = "; upm.display(tout, B); tout << ", ";
        tout << "C = "; upm.display(tout, C); tout << ", ";
        tout << "p = " << nm.to_string(zpe_upm.m().p()) << ", e = " << e << ")" << endl;
    );

    // we create a new Z_p manager, since we'll be changing the input one
    zp_manager zp_upm(upm.lim(), nm);
    zp_upm.set_zp(zpe_upm.m().p());

    // get the U, V, such that A*U + B*V = 1 (mod p)
    scoped_mpz_vector U(nm), V(nm), D(nm);
    zp_upm.ext_gcd(A.size(), A.c_ptr(), B.size(), B.c_ptr(), U, V, D);
    SASSERT(D.size() == 1 && zp_upm.m().is_one(D[0]));

    // we start lifting from (a = p, b = p, r = p)
    scoped_mpz_vector A_lifted(nm), B_lifted(nm);
    for (unsigned k = 1; k < e; k *= 2) {
        upm.checkpoint();
        // INVARIANT(a = p^e, b = p^e, r = gcd(a, b) = p^e): 
        // C = AB (mod b), UA + VB = 1 (mod a)
        // deg(U) < deg(B), dev(V) < deg(A), deg(C) = deg(A) + deg(V)
        // gcd(l(A), r) = 1
        
        // regular hensel lifting from a to b*r, here from pe -> pk*pk = p^{k*k} 
        numeral const & pe = zpe_upm.m().p();  
        
        hensel_lift(upm, pe, pe, pe, U, A, V, B, C, A_lifted, B_lifted);
        // now we have C = AB (mod b*r)
        TRACE("polynomial::factorization::bughunt", 
            tout << "A_lifted = "; upm.display(tout, A_lifted); tout << endl;
            tout << "B_lifted = "; upm.display(tout, B_lifted); tout << endl;
            tout << "C = "; upm.display(tout, C); tout << endl;
        );
        
        // we employ similar reasoning as in the regular hansel lemma now
        // we need to lift UA + VB = 1 (mod a) 
        // since after the lift, we still have UA + VB = 1 (mod a) we know that (1 - UA - VB)/a is in Z[x]
        // so we can compute g = (1 - UA - VB)/a 
        // we need U1 and V1 such that U1A + V1B = 1 (mod a^2), with U1 = U mod a, V1 = V mod a
        // hence U1 = U + aS, V1 = V + aT and we need
        // (U + aS)A + (V + aT)B = 1 (mod a^2) same as
        // UA + VB + a(SA + TB) = 1 (mod a^2) same as 
        // SA + TB = g (mod a) hence
        // (gU + tB)A + (gV - tA)B = g (mod a) will be a solution and we pick t such that deg(gV - tA) < deg(A)
        
        // compute g
        scoped_mpz_vector tmp1(nm), g(nm);
        g.push_back(numeral());
        nm.set(g.back(), 1); // g = 1
        upm.mul(A_lifted.size(), A_lifted.c_ptr(), U.size(), U.c_ptr(), tmp1); // tmp1 = AU
        upm.sub(g.size(), g.c_ptr(), tmp1.size(), tmp1.c_ptr(), g); // g = 1 - UA
        upm.mul(B_lifted.size(), B_lifted.c_ptr(), V.size(), V.c_ptr(), tmp1); // tmp1 = BV
        upm.sub(g.size(), g.c_ptr(), tmp1.size(), tmp1.c_ptr(), g); // g = 1 - UA - VB
        upm.div(g, pe);
        to_zp_manager(zpe_upm, g);
        TRACE("polynomial::factorization::bughunt", 
            tout << "g = (1 - A_lifted*U - B_lifted*V)/" << nm.to_string(pe) << endl;
            tout << "g == "; upm.display(tout, g); tout << endl;
        );

        // compute the S, T
        scoped_mpz_vector S(nm), T(nm), t(nm), tmp2(nm);
        zpe_upm.mul(g.size(), g.c_ptr(), V.size(), V.c_ptr(), tmp1); // tmp1 = gV
        zpe_upm.div_rem(tmp1.size(), tmp1.c_ptr(), A.size(), A.c_ptr(), t, T); // T = gV - tA, deg(T) < deg(A)
        zpe_upm.mul(g.size(), g.c_ptr(), U.size(), U.c_ptr(), tmp1); // tmp1 = gU
        zpe_upm.mul(t.size(), t.c_ptr(), B.size(), B.c_ptr(), tmp2); // tmp2 = tB
        zpe_upm.add(tmp1.size(), tmp1.c_ptr(), tmp2.size(), tmp2.c_ptr(), S);
        
        // now update U = U + a*S and V = V + a*T
        upm.mul(S.size(), S.c_ptr(), pe);
        upm.mul(T.size(), T.c_ptr(), pe);
        upm.add(U.size(), U.c_ptr(), S.size(), S.c_ptr(), U);
        upm.add(V.size(), V.c_ptr(), T.size(), T.c_ptr(), V); // deg(V) < deg(A), deg(T) < deg(A) => deg(V') < deg(A)

        // we go quadratic
        zpe_upm.m().set_p_sq();
        to_zp_manager(zpe_upm, U);
        to_zp_manager(zpe_upm, V);
        to_zp_manager(zpe_upm, A_lifted);
        to_zp_manager(zpe_upm, B_lifted);

        // at this point we have INVARIANT(a = (p^e)^2, b = (p^e)^2, r = (p^e)^2) 
        A.swap(A_lifted);
        B.swap(B_lifted);

        CASSERT("polynomial::factorizatio::bughunt", check_quadratic_hensel(zpe_upm, U, A, V, B));
    }
}

bool check_hensel_lift(z_manager & upm, numeral_vector const & f, zp_factors const & zp_fs, zp_factors const & zpe_fs, unsigned e) {
    numeral_manager & nm(upm.m());
    
    zp_manager & zp_upm = zp_fs.upm();
    zp_manager & zpe_upm = zpe_fs.upm();

    numeral const & p = zp_fs.nm().p();
    numeral const & pe = zpe_fs.nm().p();

    scoped_numeral power(nm);
    nm.power(p, e, power);
    if (!nm.ge(pe, power)) {
        return false;
    }
    
    // check f = lc(f) * zp_fs (mod p)
    scoped_numeral_vector mult_zp(nm), f_zp(nm);
    zp_fs.multiply(mult_zp);
    to_zp_manager(zp_upm, f, f_zp);
    zp_upm.mul(mult_zp, f_zp.back());
    if (!upm.eq(mult_zp, f_zp)) {
        TRACE("polynomial::factorization::bughunt", 
            tout << "f = "; upm.display(tout, f); tout << endl;
            tout << "zp_fs = " << zp_fs << endl;
            tout << "sage: R.<x> = Zmod(" << nm.to_string(p) << ")['x']" << endl;
            tout << "sage: mult_zp = "; upm.display(tout, mult_zp); tout << endl;
            tout << "sage: f_zp = "; upm.display(tout, f_zp); tout << endl;
            tout << "sage: mult_zp == f_zp" << endl;
        );    
        return false;
    }

    // check individual factors 
    if (zpe_fs.distinct_factors() != zp_fs.distinct_factors()) {
        return false;
    }

    // check f = lc(f) * zpe_fs (mod p^e)
    scoped_numeral_vector mult_zpe(nm), f_zpe(nm);
    zpe_fs.multiply(mult_zpe);
    to_zp_manager(zpe_upm, f, f_zpe);   
    zpe_upm.mul(mult_zpe, f_zpe.back());
    if (!upm.eq(mult_zpe, f_zpe)) {
        TRACE("polynomial::factorization::bughunt", 
            tout << "f = "; upm.display(tout, f); tout << endl;
            tout << "zpe_fs = " << zpe_fs << endl;
            tout << "sage: R.<x> = Zmod(" << nm.to_string(pe) << ")['x']" << endl;
            tout << "sage: mult_zpe = "; upm.display(tout, mult_zpe); tout << endl;
            tout << "sage: f_zpe = "; upm.display(tout, f_zpe); tout << endl;
            tout << "sage: mult_zpe == f_zpe" << endl;
        );
        return false;
    }

    return true;
}

bool check_individual_lift(zp_manager & zp_upm, numeral_vector const & A_p, zp_manager & zpe_upm, numeral_vector const & A_pe) {
    scoped_numeral_vector A_pe_p(zp_upm.m());
    to_zp_manager(zp_upm, A_pe, A_pe_p);

    if (!zp_upm.eq(A_p, A_pe_p)) {
        return false;
    }

    return true;
}

void hensel_lift(z_manager & upm, numeral_vector const & f, zp_factors const & zp_fs, unsigned e, zp_factors & zpe_fs) {
    SASSERT(zp_fs.total_factors() > 0);

    zp_numeral_manager & zp_nm = zp_fs.nm();
    zp_manager & zp_upm = zp_fs.upm();
    z_numeral_manager & nm = zp_nm.m();

    SASSERT(nm.is_one(zp_fs.get_constant()));

    zp_numeral_manager & zpe_nm = zpe_fs.nm();
    zp_manager & zpe_upm = zpe_fs.upm();
    zpe_nm.set_zp(zp_nm.p());
    
    TRACE("polynomial::factorization::bughunt", 
        tout << "polynomial::hansel_lift("; upm.display(tout, f); tout << ", " << zp_fs << ")" << endl;
    );

    // lift the factors one by one
    scoped_mpz_vector A(nm), B(nm), C(nm), f_parts(nm); // these will all be in Z_p
    
    // copy of f, that we'll be cutting parts of
    upm.set(f.size(), f.c_ptr(), f_parts);

    // F_k are factors mod Z_p, A_k the factors mod p^e
    // the invariant we keep is that:
    // (1) f_parts = C = lc(f) * \prod_{k = i}^n F_k, C in Z_p[x]
    // (2) A_k = F_k (mod p), for k < i
    // (3) f = (\prod_{k < i} A_k) * f_parts (mod p^e)
    for (int i = 0, i_end = zp_fs.distinct_factors()-1; i < i_end; ++ i) {
        SASSERT(zp_fs.get_degree(i) == 1); // p was chosen so that f is square-free
        
        // F_i = A (mod Z_p)
        zp_upm.set(zp_fs[i].size(), zp_fs[i].c_ptr(), A);
        TRACE("polynomial::factorization::bughunt", 
            tout << "A = "; upm.display(tout, A); tout << endl;
        );
        
        // C = f_parts (mod Z_p)
        if (i > 0) {
            to_zp_manager(zp_upm, f_parts, C);
        } 
        else {
            // first time around, we don't have p^e yet, so first time we just compute C 
            zp_fs.multiply(C);
            scoped_mpz lc(nm);
            zp_nm.set(lc, f.back());
            zp_upm.mul(C, lc);
        }
        TRACE("polynomial::factorization::bughunt", 
            tout << "C = "; upm.display(tout, C); tout << endl;
        );

        // we take B to be what's left from C and A
        zp_upm.div(C.size(), C.c_ptr(), A.size(), A.c_ptr(), B);
        TRACE("polynomial::factorization::bughunt", 
            tout << "B = "; upm.display(tout, B); tout << endl;
        );

        // lift A and B to p^e (this will change p^e and put it zp_upm)
        zpe_nm.set_zp(zp_nm.p());
        hensel_lift_quadratic(upm, f_parts, zpe_upm, A, B, e);
        CASSERT("polynomial::factorizatio::bughunt", check_individual_lift(zp_upm, zp_fs[i], zpe_upm, A));
        TRACE("polynomial::factorization", 
            tout << "lifted to " << nm.to_string(zpe_upm.m().p()) << endl;        
            tout << "A = "; upm.display(tout, A); tout << endl;
            tout << "B = "; upm.display(tout, B); tout << endl;
        );
        
        // if this is the first time round, we also construct f_parts (now we have correct p^e)
        if (i == 0) {
            to_zp_manager(zpe_upm, f, f_parts);
        }
        
        // take the lifted A out of f_parts
        zpe_upm.div(f_parts.size(), f_parts.c_ptr(), A.size(), A.c_ptr(), f_parts);
        
        // add the lifted factor (kills A)
        zpe_fs.push_back_swap(A, 1);
    }

    // we have one last factor, but it also contains lc(f), so take it out
    scoped_mpz lc_inv(nm);
    zpe_nm.set(lc_inv, f.back());
    zpe_nm.inv(lc_inv);
    zpe_upm.mul(B, lc_inv);
    zpe_fs.push_back_swap(B, 1);

    TRACE("polynomial::factorization::bughunt", 
        tout << "polynomial::hansel_lift("; upm.display(tout, f); tout << ", " << zp_fs << ") => " << zpe_fs << endl;
    );

    CASSERT("polynomial::factorizatio::bughunt", check_hensel_lift(upm, f, zp_fs, zpe_fs, e));
}

// get a bound on B for the factors of f with degree less or equal to deg(f)/2
// and then choose e to be smallest such that p^e > 2*lc(f)*B, we use the mignotte
// 
// from [3, pg 134] 
// |p| = sqrt(\sum |p_i|^2). If a = \sum a_i x^i, b = \sum b_j, deg b = n, and b divides a, then for all j 
// 
//                 |b_j| <= (n-1 over j)|a| + (n-1 over j-1)|lc(a)|
//
// when factoring a polynomial, we find a bound B for a factor of f of degree <= deg(f)/2
// allowing both positive and negative as coefficients of b, we now want a power p^e such that all coefficients
// can be represented, i.e. [-B, B] \subset [-\ceil(p^e/2), \ceil(p^e)/2], so we peek e, such that p^e >= 2B

static unsigned mignotte_bound(z_manager & upm, numeral_vector const & f, numeral const & p) {
    numeral_manager & nm = upm.m();

    SASSERT(upm.degree(f) >= 2);
    unsigned n = upm.degree(f)/2; // >= 1

    // get the approximation for the norm of a
    scoped_numeral f_norm(nm);
    for (unsigned i = 0; i < f.size(); ++ i) {
        if (!nm.is_zero(f[i])) {
            nm.addmul(f_norm, f[i], f[i], f_norm);
        }
    }
    nm.root(f_norm, 2);

    // by above we can pick (n-1 over (n-1/2))|a| + (n-1 over (n-1)/2)lc(a)
    // we approximate both binomial-coefficients with 2^(n-1), so to get 2B we use 2^n(f_norm + lc(f))
    scoped_numeral bound(nm); 
    nm.set(bound, 1);
    nm.mul2k(bound, n, bound);
    scoped_numeral tmp(nm);
    nm.set(tmp, f.back());
    nm.abs(tmp);
    nm.add(f_norm, tmp, f_norm);
    nm.mul(bound, f_norm, bound);

    // we need e such that p^e >= B    
    nm.set(tmp, p);
    unsigned e;
    for (e = 1; nm.le(tmp, bound); e *= 2) {
        nm.mul(tmp, tmp, tmp);
    }

    return e;
}

/**
   \brief Given f from Z[x] that is square free, it factors it.
   This method also assumes f is primitive.
*/
bool factor_square_free(z_manager & upm, numeral_vector const & f, factors & fs, unsigned k, factor_params const & params) {
    TRACE("polynomial::factorization::bughunt", 
        tout << "sage: f = "; upm.display(tout, f); tout << endl;
        tout << "sage: if (not f.is_squarefree()): print 'Error, f is not square-free'" << endl;
        tout << "sage: print 'Factoring :', f" << endl;
        tout << "sage: print 'Expected factors: ', f.factor()" << endl;
    );    

    numeral_manager & nm = upm.m();

    // This method assumes f is primitive. Thus, the content of f must be one
    DEBUG_CODE({
        scoped_numeral f_cont(nm);
        nm.gcd(f.size(), f.c_ptr(), f_cont);
        SASSERT(f.size() == 0 || nm.is_one(f_cont));
    });

    scoped_numeral_vector f_pp(nm);
    upm.set(f.size(), f.c_ptr(), f_pp);
    
    // make sure the leading coefficient is positive
    if (!f_pp.empty() && nm.is_neg(f_pp[f_pp.size() - 1])) {
        for (unsigned i = 0; i < f_pp.size(); i++)
            nm.neg(f_pp[i]);
        // flip sign constant if k is odd
        if (k % 2 == 1) {
            scoped_numeral c(nm);
            nm.set(c, fs.get_constant());
            nm.neg(c);
            fs.set_constant(c);
        }
    }

    TRACE("polynomial::factorization::bughunt", 
        tout << "sage: f_pp = "; upm.display(tout, f_pp); tout << endl;
        tout << "sage: if (not (f_pp * 1 == f): print 'Error, content computation wrong'" << endl;
    ); 

    // the variables we'll be using and updating in Z_p
    scoped_numeral p(nm); 
    nm.set(p, 2);
    zp_manager zp_upm(upm.lim(), nm.m());
    zp_upm.set_zp(p);
    zp_factors zp_fs(zp_upm);
    scoped_numeral zp_fs_p(nm); nm.set(zp_fs_p, 2);
    
    // we keep all the possible sets of degrees of factors in this set
    factorization_degree_set degree_set(zp_upm);

    // we try get some number of factorizations in Z_p, for some primes
    // get the prime p such that 
    // (1) (f_prim mod p) stays square-free
    // (2) l(f_prim) mod p doesn't vanish, i.e. we don't get a polynomial of smaller degree            
    prime_iterator prime_it;
    scoped_numeral gcd_tmp(nm);    
    unsigned trials = 0;
    TRACE("polynomial::factorization::bughunt", tout << "trials: " << params.m_p_trials << "\n";);
    while (trials <= params.m_p_trials) {
        upm.checkpoint();
        // construct prime to check 
        uint64_t next_prime = prime_it.next();
        if (next_prime > params.m_max_p) {
            fs.push_back(f_pp, k);
            return false;
        }
        nm.set(p, next_prime);
        zp_upm.set_zp(p);

        // we need gcd(lc(f_pp), p) = 1
        nm.gcd(p, f_pp.back(), gcd_tmp);
        TRACE("polynomial::factorization::bughunt", 
            tout << "sage: if (not (gcd(" << nm.to_string(p) << ", " << nm.to_string(f_pp.back()) << ")) == " << 
              nm.to_string(gcd_tmp) << "): print 'Error, wrong gcd'" << endl;
        );    
        if (!nm.is_one(gcd_tmp)) {
            continue;
        }
    
        // if it's not square free, we also try something else
        scoped_numeral_vector f_pp_zp(nm);
        to_zp_manager(zp_upm, f_pp, f_pp_zp);

        TRACE("polynomial::factorization::bughunt", 
            tout << "sage: Rp.<x_p> = GF(" << nm.to_string(p) << ")['x_p']"; tout << endl;
            tout << "sage: f_pp_zp = "; zp_upm.display(tout, f_pp_zp, "x_p"); tout << endl;
        );    

        if (!zp_upm.is_square_free(f_pp_zp.size(), f_pp_zp.c_ptr()))
            continue;
        
        // we make it monic
        zp_upm.mk_monic(f_pp_zp.size(), f_pp_zp.c_ptr());

        // found a candidate, factorize in Z_p and add back the constant
        zp_factors current_fs(zp_upm);
        bool factored = zp_factor_square_free(zp_upm, f_pp_zp, current_fs);        
        if (!factored) {
            fs.push_back(f_pp, k);
            return true;
        }

        // get the factors degrees set
        factorization_degree_set current_degree_set(current_fs);
        if (degree_set.max_degree() == 0) {
            // first time, initialize
            degree_set.swap(current_degree_set);
        } 
        else {
            degree_set.intersect(current_degree_set);
        }

        // if the degree set is trivial, we are done
        if (degree_set.is_trivial()) {
            fs.push_back(f_pp, k);
            return true;
        }

        // we found a candidate, lets keep it if it has less factors than the current best
        trials ++;
        if (zp_fs.distinct_factors() == 0 || zp_fs.total_factors() > current_fs.total_factors()) {
            zp_fs.swap(current_fs);
            nm.set(zp_fs_p, p);

            TRACE("polynomial::factorization::bughunt", 
                tout << "best zp factorization (Z_" << nm.to_string(zp_fs_p) << "): ";
                tout << zp_fs << endl;
                tout << "best degree set: "; degree_set.display(tout); tout << endl;
            );
        }
    }
#ifndef _EXTERNAL_RELEASE 
    IF_VERBOSE(FACTOR_VERBOSE_LVL, verbose_stream() << "(polynomial-factorization :at GF_" << nm.to_string(zp_upm.p()) << ")" << std::endl;);
#endif
    
    // make sure to set the zp_manager back to modulo zp_fs_p 
    zp_upm.set_zp(zp_fs_p);
    
    TRACE("polynomial::factorization::bughunt", 
          tout << "best zp factorization (Z_" << nm.to_string(zp_fs_p) << "): " << zp_fs << endl;
          tout << "best degree set: "; degree_set.display(tout); tout << endl;
          );
    
    // get a bound on B for the factors of f_pp with degree less or equal to deg(f)/2
    // and then choose e to be smallest such that p^e > 2*lc(f)*B, we use the mignotte
    unsigned e = mignotte_bound(upm, f_pp, zp_fs_p);
    TRACE("polynomial::factorization::bughunt", 
          tout << "out p = " << nm.to_string(zp_fs_p) << ", and we'll work p^e for e = " << e << endl;
          );
    
    // we got a prime factoring, so we do the lifting now
    zp_manager zpe_upm(upm.lim(), nm.m());
    zpe_upm.set_zp(zp_fs_p);
    zp_numeral_manager & zpe_nm = zpe_upm.m();
    
    zp_factors zpe_fs(zpe_upm);
    // this might give something bigger than p^e, but the lifting procedure will update the zpe_nm
    // zp factors are monic, so will be the zpe factors, i.e. f_pp = zpe_fs * lc(f_pp) (mod p^e)
    hensel_lift(upm, f_pp, zp_fs, e, zpe_fs); 
    
#ifndef _EXTERNAL_RELEASE 
    IF_VERBOSE(FACTOR_VERBOSE_LVL, verbose_stream() << "(polynomial-factorization :num-candidate-factors " << zpe_fs.distinct_factors() << ")" << std::endl;);
#endif
    
    // the leading coefficient of f_pp mod p^e
    scoped_numeral f_pp_lc(nm);
    zpe_nm.set(f_pp_lc, f_pp.back());
    
    // we always keep in f_pp the actual primitive part f_pp*lc(f_pp)
    upm.mul(f_pp, f_pp_lc);
    
    // now we go through the combinations of factors to check construct the factorization
    ufactorization_combination_iterator it(zpe_fs, degree_set);
    scoped_numeral_vector trial_factor(nm), trial_factor_quo(nm);
    scoped_numeral trial_factor_cont(nm);
    TRACE("polynomial::factorization::bughunt", 
          tout << "STARTING TRIAL DIVISION" << endl;
          tout << "zpe_fs" << zpe_fs << endl;
          tout << "degree_set = "; degree_set.display(tout); tout << endl;
          );
    bool result = true;
    bool remove = false;
    unsigned counter = 0;
    while (it.next(remove)) {
        upm.checkpoint();
        counter++;
        if (counter > params.m_max_search_size) {
            // stop search
            result = false;
            break;
        }
        //
        // our bound ensures we can extract the right factors of degree at most 1/2 of the original
        // so, if out trial factor has degree bigger than 1/2, we need to take the rest of the factors
        // but, if we take the rest and it works, it doesn't mean that the rest is factorized, so we still take out
        // the original factor
        bool using_left = it.current_degree() <= zp_fs.get_degree()/2;
        if (using_left) {
            // do a quick check first
            scoped_numeral tmp(nm);
            it.get_left_tail_coeff(f_pp_lc, tmp);
            if (!nm.divides(tmp, f_pp[0])) {
                // don't remove this combination
                remove = false;
                continue;
            }
            it.left(trial_factor);
        } 
        else {
            // do a quick check first
            scoped_numeral tmp(nm);
            it.get_right_tail_coeff(f_pp_lc, tmp);
            if (!nm.divides(tmp, f_pp[0])) {
                // don't remove this combination
                remove = false;
                continue;
            }
            it.right(trial_factor);
        }

        // add the lc(f_pp) to the trial divisor
        zpe_upm.mul(trial_factor, f_pp_lc);
        TRACE("polynomial::factorization::bughunt", 
            tout << "f_pp*lc(f_pp) = "; upm.display(tout, f_pp); tout << endl;
            tout << "trial_factor = "; upm.display(tout, trial_factor); tout << endl;    
        );

        bool true_factor = upm.exact_div(f_pp, trial_factor, trial_factor_quo);        
        
        TRACE("polynomial::factorization::bughunt", 
            tout << "trial_factor = "; upm.display(tout, trial_factor); tout << endl;    
            tout << "trial_factor_quo = "; upm.display(tout, trial_factor_quo); tout << endl;
            tout << "result = " << (true_factor ? "true" : "false") << endl;
        );

        // if division is precise we have a factor
        if (true_factor) {
            if (!using_left) {
                // as noted above, we still use the original factor
                trial_factor.swap(trial_factor_quo);
            }
            // We need to get the content out of the factor 
            upm.get_primitive_and_content(trial_factor, trial_factor, trial_factor_cont);
            // add the factor
            fs.push_back(trial_factor, k);
            // we continue with the quotient (with the content added back)
            // but we also have to keep lc(f_pp)*f_pp
            upm.get_primitive_and_content(trial_factor_quo, f_pp, trial_factor_cont);
            nm.set(f_pp_lc, f_pp.back());
            upm.mul(f_pp, f_pp_lc);
            // but we also remove it from the iterator
            remove = true;
        } 
        else {
            // don't remove this combination
            remove = false;
        }
        TRACE("polynomial::factorization::bughunt", 
            tout << "factors = " << fs << endl;
            tout << "f_pp*lc(f_pp) = "; upm.display(tout, f_pp); tout << endl;
            tout << "lc(f_pp) = " << f_pp_lc << endl;
        );
    }
#ifndef _EXTERNAL_RELEASE 
    IF_VERBOSE(FACTOR_VERBOSE_LVL, verbose_stream() << "(polynomial-factorization :search-size " << counter << ")" << std::endl;);
#endif

    // add the what's left to the factors (if not a constant)
    if (f_pp.size() > 1) {
        upm.div(f_pp, f_pp_lc);
        fs.push_back(f_pp, k);
    } 
    else {
        // if a constant it must be 1 (it was primitive)
        SASSERT(f_pp.size() == 1 && nm.is_one(f_pp.back()));
    }

    return result;
}

bool factor_square_free(z_manager & upm, numeral_vector const & f, factors & fs, factor_params const & params) {
    return factor_square_free(upm, f, fs, 1, params);
}

}; // end upolynomial namespace
