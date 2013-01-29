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
#include"mpz_matrix.h"
#include"buffer.h"

mpz_matrix_manager::mpz_matrix_manager(unsynch_mpz_manager & nm, small_object_allocator & a):
    m_nm(nm),
    m_allocator(a) {
}

mpz_matrix_manager::~mpz_matrix_manager() {
}

void mpz_matrix_manager::mk(unsigned m, unsigned n, mpz_matrix & A) {
    SASSERT(m > 0 && n > 0);
    del(A);
    A.m = m;
    A.n = n;
    void * mem = m_allocator.allocate(sizeof(mpz)*m*n);
    A.a_ij = new (mem) mpz[m*n];
}

void mpz_matrix_manager::del(mpz_matrix & A) {
    if (A.a_ij != 0) {
        for (unsigned i = 0; i < A.m; i++)
            for (unsigned j = 0; j < A.n; j++)
                nm().del(A(i,j));
        unsigned sz = sizeof(mpz) * A.m * A.n;
        m_allocator.deallocate(sz, A.a_ij);
        A.m = 0;
        A.n = 0;
        A.a_ij = 0;
    }
}

void mpz_matrix_manager::set(mpz_matrix & A, mpz_matrix const & B) {
    if (&A == &B)
        return;
    if (A.m != B.m || A.n != B.n) {
        del(A);
        mk(B.m, B.n, A);
    }
    SASSERT(A.m == B.m && A.n == B.n);
    for (unsigned i = 0; i < B.m; i++)
        for (unsigned j = 0; j < B.n; j++)
            nm().set(A(i, j), B(i, j));
}

void mpz_matrix_manager::tensor_product(mpz_matrix const & A, mpz_matrix const & B, mpz_matrix & C) {
    scoped_mpz_matrix CC(*this);
    mk(A.m * B.m, A.n * B.n, CC);
    for (unsigned i = 0; i < CC.m(); i++)
        for (unsigned j = 0; j < CC.n(); j++)
            nm().mul(A(i / B.m, j / B.n), 
                     B(i % B.m, j % B.n), 
                     CC(i, j));
    C.swap(CC);
}

void mpz_matrix_manager::swap_rows(mpz_matrix & A, unsigned i, unsigned j) {
    if (i != j) {
        for (unsigned k = 0; k < A.n; k++) 
            ::swap(A(i, k), A(j, k));
    }
}

// If b_i == 0, then method just divides the given row by its GCD
// If b_i != 0
//     If the GCD of the row divides *b_i
//        divide the row and *b_i by the GCD
//     Else
//        If int_solver == true ==> return false (the system is unsolvable)
bool mpz_matrix_manager::normalize_row(mpz * A_i, unsigned n, mpz * b_i, bool int_solver) {
    scoped_mpz g(nm());
    bool first = true;
    for (unsigned j = 0; j < n; j++) {
        if (nm().is_zero(A_i[j]))
            continue;
        if (first) {
            nm().set(g, A_i[j]);
            nm().abs(g);
            first = false;
        }
        else {
            nm().gcd(g, A_i[j], g);
        }
        if (nm().is_one(g))
            return true;
    }
    if (first)
        return true; // zero row
    if (!nm().is_one(g)) {
        if (b_i) {
            if (nm().divides(g, *b_i)) {
                for (unsigned j = 0; j < n; j++) {
                    nm().div(A_i[j], g, A_i[j]);
                }
                nm().div(*b_i, g, *b_i);
            }
            else {
                if (int_solver)
                    return false; // system does not have an integer solution
            }
        }
        else {
            for (unsigned j = 0; j < n; j++) {
                nm().div(A_i[j], g, A_i[j]);
            }
        }
    }
    return true;
}

/*
     Given a matrix of the form

               k2
               |
               V
     X X ... X X ... X   
     0 X ... X X ... X 
     ... ... X X ... X
k1=> 0 0 ... 0 X ... X
     0 0 ... 0 X ... X
     ... ... 0 X ... X
     0 0 ... 0 X ... X 

     It will "zero" the elements a_{k1+1, k2} ... a_{m, k2} by addining multiples of the row k1 to multiples of the 
     rows k1+1, ..., m

     The resultant matrix will look like 

               k2
               |
               V
     X X ... X X ... X   
     0 X ... X X ... X 
     ... ... X X ... X
k1=> 0 0 ... 0 X ... X
     0 0 ... 0 0 ... X
     ... ... 0 0 ... X
     0 0 ... 0 0 ... X 
     
     
     If b != 0, then the transformations are also applied to b.
     If int_solver == true and b != 0, then the method returns false if when
     performing the transformations it detected that it is impossible to
     solve the integer system of equations A x = b.
*/
bool mpz_matrix_manager::eliminate(mpz_matrix & A, mpz * b, unsigned k1, unsigned k2, bool int_solver) {
    // check if first k2-1 positions of row k1 are 0
    DEBUG_CODE(for (unsigned j = 0; j < k2; j++) { SASSERT(nm().is_zero(A(k1, j))); });
    mpz & a_kk = A(k1, k2);
    SASSERT(!nm().is_zero(a_kk));
    scoped_mpz t1(nm()), t2(nm());
    scoped_mpz a_ik_prime(nm()), a_kk_prime(nm()), lcm_a_kk_a_ik(nm());
    // for all rows below pivot
    for (unsigned i = k1+1; i < A.m; i++) {
        // check if first k-1 positions of row k are 0
        DEBUG_CODE(for (unsigned j = 0; j < k2; j++) { SASSERT(nm().is_zero(A(i, j))); });
        mpz & a_ik = A(i, k2);
        if (!nm().is_zero(a_ik)) {
            // a_ik' = lcm(a_kk, a_ik)/a_kk
            // a_kk' = lcm(a_kk, a_ik)/a_ik
            nm().lcm(a_kk, a_ik, lcm_a_kk_a_ik);
            nm().div(lcm_a_kk_a_ik, a_kk, a_ik_prime);
            nm().div(lcm_a_kk_a_ik, a_ik, a_kk_prime);
            for (unsigned j = k2+1; j < A.n; j++) {
                // a_ij <- a_kk' * a_ij - a_ik' * a_kj
                nm().mul(a_ik_prime, A(k1, j), t1);
                nm().mul(a_kk_prime, A(i, j), t2);
                nm().sub(t2, t1, A(i, j));
            }
            if (b) {
                // b_i <- a_kk' * b_i - a_ik' * b_k
                nm().mul(a_ik_prime, b[k1], t1);
                nm().mul(a_kk_prime, b[i], t2);
                nm().sub(t2, t1, b[i]);
            }
            // a_ik <- 0
            nm().set(A(i, k2), 0);
            // normalize row i
            if (!normalize_row(A.row(i), A.n, b ? &(b[i]) : 0, int_solver))
                return false;
        }
        SASSERT(nm().is_zero(A(i, k2)));
    }
    return true;
}

bool mpz_matrix_manager::solve_core(mpz_matrix const & _A, mpz * b, bool int_solver) {
    SASSERT(_A.n == _A.m);
    scoped_mpz_matrix A(*this);
    set(A, _A);
    for (unsigned k = 0; k < A.m(); k++) {
        TRACE("mpz_matrix", 
              tout << "k: " << k << "\n" << A;
              tout << "b:";
              for (unsigned i = 0; i < A.m(); i++) {
                  tout << " ";
                  nm().display(tout, b[i]); 
              }
              tout << "\n";);
        // find pivot
        unsigned i = k;
        for (; i < A.m(); i++) {
            if (!nm().is_zero(A(i, k)))
                break;
        }
        if (i == A.m())
            return false; // matrix is singular
        // swap rows k and i
        swap_rows(A, k, i);
        swap(b[k], b[i]);
        // 
        if (!eliminate(A, b, k, k, int_solver))
            return false;
    }
    // Back substitution
    unsigned k = A.m();
    while (k > 0) {
        --k;
        DEBUG_CODE(for (unsigned j = 0; j < A.n(); j++) { SASSERT(j == k || nm().is_zero(A(k, j))); });
        SASSERT(!nm().is_zero(A(k, k)));
        if (nm().divides(A(k, k), b[k])) {
            nm().div(b[k], A(k, k), b[k]);
            nm().set(A(k, k), 1);
        }
        else {
            if (int_solver)
                return false; // no integer solution
            if (nm().is_neg(A(k, k))) {
                nm().neg(A(k, k));
                nm().neg(b[k]);
            }
        }
        if (!int_solver) {
            // REMARK: 
            // For the sign determination algorithm, we only use int_solver == true.
            //
            // TODO: implement backward substitution when int_solver == false
            // In this case, A(k, k) may not be 1.
            NOT_IMPLEMENTED_YET();
        }
        SASSERT(!int_solver || nm().is_one(A(k, k)));
        // back substitute
        unsigned i = k;
        while (i > 0) {
            --i;
            // Assuming int_solver == true
            SASSERT(int_solver); // See comment above
            // b_i <- b_i - a_ik * b_k
            nm().submul(b[i], A(i, k), b[k], b[i]);
            nm().set(A(i, k), 0);
        }
    }
    return true;
}

bool mpz_matrix_manager::solve(mpz_matrix const & A, mpz * b, mpz const * c) {
    for (unsigned i = 0; i < A.n; i++)
        nm().set(b[i], c[i]);
    return solve_core(A, b, true);
}

bool mpz_matrix_manager::solve(mpz_matrix const & A, int * b, int const * c) {
    scoped_mpz_matrix _b(*this);
    mk(A.n, 1, _b);
    for (unsigned i = 0; i < A.n; i++)
        nm().set(_b(i,0), c[i]);
    bool r = solve_core(A, _b.A.a_ij, true);
    if (r) {
        for (unsigned i = 0; i < A.n; i++)
            b[i] = _b.get_int(i, 0);
    }
    return r;
}

void mpz_matrix_manager::filter_cols(mpz_matrix const & A, unsigned num_cols, unsigned const * cols, mpz_matrix & B) {
    SASSERT(num_cols <= A.n);
    // Check pre-condition: 
    //   - All elements in cols are smaller than A.n
    //   - cols is sorted
    //   - cols does not contain repeated elements
    DEBUG_CODE({
            for (unsigned i = 0; i < num_cols; i ++) {
                SASSERT(cols[i] < A.n);
                SASSERT(i == 0 || cols[i-1] < cols[i]);
            }
        });
    if (num_cols == A.n) {
        // keep everything
        set(B, A); 
    }
    else {
        SASSERT(num_cols < A.n);
        scoped_mpz_matrix C(*this);
        mk(A.m, num_cols, C);
        for (unsigned i = 0; i < A.m; i++) 
            for (unsigned j = 0; j < num_cols; j++) 
                nm().set(C(i, j), A(i, cols[j]));
        B.swap(C);
    }
}

void mpz_matrix_manager::permute_rows(mpz_matrix const & A, unsigned const * p, mpz_matrix & B) {
    // Check if p is really a permutation
    DEBUG_CODE({ 
            buffer<bool> seen;
            seen.resize(A.m, false);
            for (unsigned i = 0; i < A.m; i++) {
                SASSERT(p[i] < A.m);
                SASSERT(!seen[p[i]]);
                seen[p[i]] = true;
            }
        });
    scoped_mpz_matrix C(*this);
    mk(A.m, A.n, C);
    for (unsigned i = 0; i < A.m; i++) 
        for (unsigned j = 0; j < A.n; j++)
            nm().set(C(i, j), A(p[i], j));
    B.swap(C);
}

unsigned mpz_matrix_manager::linear_independent_rows(mpz_matrix const & _A, unsigned * r, mpz_matrix & B) {
    unsigned r_sz = 0;
    scoped_mpz_matrix A(*this);
    scoped_mpz g(nm());
    scoped_mpz t1(nm()), t2(nm());
    scoped_mpz a_ik_prime(nm()), a_kk_prime(nm()), lcm_a_kk_a_ik(nm());
    set(A, _A);
    sbuffer<unsigned, 128> rows;
    rows.resize(A.m(), 0);
    for (unsigned i = 0; i < A.m(); i++)
        rows[i] = i;
    for (unsigned k1 = 0, k2 = 0; k1 < A.m(); k1++) {
        TRACE("mpz_matrix", tout << "k1: " << k1 << ", k2: " << k2 << "\n" << A;);
        // find pivot
        unsigned pivot = UINT_MAX;
        for (unsigned i = k1; i < A.m(); i++) {
            if (!nm().is_zero(A(i, k2))) {
                if (pivot == UINT_MAX) {
                    pivot = i;
                }
                else {
                    if (rows[i] < rows[pivot])
                        pivot = i;
                }
            }
        }
        if (pivot == UINT_MAX)
            continue;
        // swap rows k and pivot
        swap_rows(A, k1, pivot);
        std::swap(rows[k1], rows[pivot]);
        // 
        r[r_sz] = rows[k1];
        r_sz++;
        if (r_sz >= A.n())
            break;
        eliminate(A, 0, k1, k2, false);
        k2++;
    }
    std::sort(r, r + r_sz);
    // Copy linear independent rows to B
    mpz_matrix & C = A;
    mk(r_sz, _A.n, C);
    for (unsigned i = 0; i < r_sz; i++ ) {
        for (unsigned j = 0; j < _A.n; j++) {
            nm().set(C(i, j), _A(r[i], j));
        }
    }
    B.swap(C);
    return r_sz;
}

void mpz_matrix_manager::display(std::ostream & out, mpz_matrix const & A, unsigned cell_width) const {
    out << A.m << " x " << A.n << " Matrix\n";
    for (unsigned i = 0; i < A.m; i++) {
        for (unsigned j = 0; j < A.n; j++) {
            if (j > 0)
                out << " ";
            std::string s = nm().to_string(A(i, j));
            if (s.size() < cell_width) {
                unsigned space = cell_width - static_cast<unsigned>(s.size());
                for (unsigned k = 0; k < space; k++) 
                    out << " ";
            }
            out << s;
        }
        out << "\n";
    }
}
