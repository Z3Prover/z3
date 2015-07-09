/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    mpz_matrix.h

Abstract:

    Matrix with integer coefficients. This is not a general purpose
    module for handling matrices with integer coefficients.  Instead,
    it is a custom package that only contains operations needed to
    implement Sign Determination (Algorithm 10.11) in the Book:
        "Algorithms in real algebraic geometry", Basu, Pollack, Roy

    Design choices: 
      - Dense representation. The matrices in Alg 10.11 are small and dense.
      - Integer coefficients instead of rational coefficients (it only complicates the solver a little bit).
        Remark: in Algorithm 10.11, the coefficients of the input matrices are always in {-1, 0, 1}.
        During solving, bigger coefficients are produced, but they are usually very small. It may be
        an overkill to use mpz instead of int. We use mpz just to be safe. 
        Remark: We do not use rational arithmetic. The solver is slightly more complicated with integers, but is saves space.

Author:

    Leonardo (leonardo) 2013-01-07

Notes:

--*/
#ifndef MPZ_MATRIX_H_
#define MPZ_MATRIX_H_

#include"mpz.h"

/**
   \brief A mxn matrix. 
   Remark: Algorithm 10.11 only uses square matrices, but supporting 
   arbitrary matrices does not increase the complexity of this module.
*/
class mpz_matrix {
    friend class mpz_matrix_manager;
    friend class scoped_mpz_matrix;
    unsigned m; 
    unsigned n;
    mpz *    a_ij;
public:
    mpz_matrix():m(0), n(0), a_ij(0) {}
    mpz const & operator()(unsigned i, unsigned j) const { 
        SASSERT(i < m); 
        SASSERT(j < n); 
        return a_ij[i*n + j]; }
    mpz & operator()(unsigned i, unsigned j) { SASSERT(i < m); SASSERT(j < n); return a_ij[i*n + j]; }
    void swap(mpz_matrix & B) { std::swap(m, B.m); std::swap(n, B.n); std::swap(a_ij, B.a_ij); }
    mpz * row(unsigned i) const { SASSERT(i < m); return a_ij + i*n; }
};

class mpz_matrix_manager {
    unsynch_mpz_manager &    m_nm;
    small_object_allocator & m_allocator;
    static void swap_rows(mpz_matrix & A, unsigned i, unsigned j);
    bool normalize_row(mpz * A_i, unsigned n, mpz * b_i, bool int_solver);
    bool eliminate(mpz_matrix & A, mpz * b, unsigned k1, unsigned k2, bool int_solver);
    bool solve_core(mpz_matrix const & A, mpz * b, bool int_solver);
public:
    mpz_matrix_manager(unsynch_mpz_manager & nm, small_object_allocator & a);
    ~mpz_matrix_manager();
    unsynch_mpz_manager & nm() const { return m_nm; }
    void mk(unsigned m, unsigned n, mpz_matrix & A);
    void del(mpz_matrix & r);
    void set(mpz_matrix & A, mpz_matrix const & B);
    void tensor_product(mpz_matrix const & A, mpz_matrix const & B, mpz_matrix & C);
    /**
       \brief Solve A*b = c
       
       Return false if the system does not have an integer solution.
       
       \pre A is a square matrix
       \pre b and c are vectors of size A.n (== A.m)
    */
    bool solve(mpz_matrix const & A, mpz * b, mpz const * c);
    /**
       \brief Solve A*b = c
       
       Return false if the system does not have an integer solution.
       
       \pre A is a square matrix
       \pre b and c are vectors of size A.n (== A.m)
    */
    bool solve(mpz_matrix const & A, int * b, int const * c);
    /**
       \brief Store in B that contains the subset cols of columns of A.
       
       \pre num_cols <= A.n
       \pre Forall i < num_cols, cols[i] < A.n
       \pre Forall 0 < i < num_cols, cols[i-1] < cols[i]
    */
    void filter_cols(mpz_matrix const & A, unsigned num_cols, unsigned const * cols, mpz_matrix & B);
    /**
       \brief Store in B the matrix obtained after applying the given permutation to the rows of A.
    */
    void permute_rows(mpz_matrix const & A, unsigned const * p, mpz_matrix & B);
    /**
       \brief Store in r the row (ids) of A that are linear independent.
       
       \remark If there is an option between rows i and j, 
       this method will give preference to the row that occurs first.
       
       \remark The vector r must have at least A.n() capacity
       The numer of linear independent rows is returned.

       Store the new matrix in B.
    */
    unsigned linear_independent_rows(mpz_matrix const & A, unsigned * r, mpz_matrix & B);

    // method for debugging purposes
    void display(std::ostream & out, mpz_matrix const & A, unsigned cell_width=4) const;
};

class scoped_mpz_matrix {
    friend class mpz_matrix_manager;
    mpz_matrix_manager & m_manager;
    mpz_matrix           A;
public:
    scoped_mpz_matrix(mpz_matrix_manager & m):m_manager(m) {}
    scoped_mpz_matrix(mpz_matrix const & B, mpz_matrix_manager & m):m_manager(m) { m_manager.set(A, B); }
    ~scoped_mpz_matrix() { m_manager.del(A); }
    mpz_matrix_manager & mm() const { return m_manager; }
    unsynch_mpz_manager & nm() const { return mm().nm(); }

    unsigned m() const { return A.m; }
    unsigned n() const { return A.n; }
    mpz * row(unsigned i) const { return A.row(i); }

    operator mpz_matrix const &() const { return A; }
    operator mpz_matrix &() { return A; }
    mpz_matrix const & get() const { return A; }
    mpz_matrix & get() { return A; }

    void swap(mpz_matrix & B) { A.swap(B); }

    void set(unsigned i, unsigned j, mpz const & v) { nm().set(A(i, j), v); }
    void set(unsigned i, unsigned j, int v) { nm().set(A(i, j), v); }

    mpz const & operator()(unsigned i, unsigned j) const { return A(i, j); }
    mpz & operator()(unsigned i, unsigned j) { return A(i, j); }

    int get_int(unsigned i, unsigned j) const { SASSERT(nm().is_int(A(i, j))); return nm().get_int(A(i, j)); }
};

inline std::ostream & operator<<(std::ostream & out, scoped_mpz_matrix const & m) {
    m.mm().display(out, m);
    return out;
}

#endif
