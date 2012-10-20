/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    linear_eq_solver.h

Abstract:

    Simple equational solver template for any number field.
    No special optimization, just the basics for solving small systems.
    It is a solver target to dense system of equations.
    Main client: Sparse Modular GCD algorithm. 
    
Author:

    Leonardo (leonardo) 2012-01-22

Notes:

--*/
#ifndef _LINEAR_EQ_SOLVER_H_
#define _LINEAR_EQ_SOLVER_H_

template<typename numeral_manager> 
class linear_eq_solver {
    typedef typename numeral_manager::numeral numeral;
    numeral_manager &         m;
    unsigned                  n; // number of variables
    vector<svector<numeral> > A;
    svector<numeral>          b;
public:
    linear_eq_solver(numeral_manager & _m):m(_m), n(0) { SASSERT(m.field()); }
    ~linear_eq_solver() { flush(); }
    
    void flush() {
        SASSERT(b.size() == A.size());
        unsigned sz = A.size();
        for (unsigned i = 0; i < sz; i++) {
            svector<numeral> & as = A[i];
            m.del(b[i]);
            SASSERT(as.size() == n);
            for (unsigned j = 0; j < n; j++) 
                m.del(as[j]);
        }
        A.reset();
        b.reset();
        n = 0;
    }

    void resize(unsigned _n) {
        if (n != _n) {
            flush();
            n = _n;
            for (unsigned i = 0; i < n; i++) {
                A.push_back(svector<numeral>());
                svector<numeral> & as = A.back();
                for (unsigned j = 0; j < n; j++) {
                    as.push_back(numeral());
                }
                b.push_back(numeral());
            }
        }
    }

    void reset() {
        for (unsigned i = 0; i < n; i++) {
            svector<numeral> & A_i = A[i];
            for (unsigned j = 0; j < n; j++) {
                m.set(A_i[j], 0);
            }
            m.set(b[i], 0);
        }
    }
    
    // Set row i with _as[0]*x_0 + ... + _as[n-1]*x_{n-1} = b
    void add(unsigned i, numeral const * _as, numeral const & _b) {
        SASSERT(i < n);
        m.set(b[i], _b);
        svector<numeral> & A_i = A[i];
        for (unsigned j = 0; j < n; j++) {
            m.set(A_i[j], _as[j]);
        }
    }
    
    // Return true if the system of equations has a solution.
    // Return false if the matrix is singular
    bool solve(numeral * xs) {
        for (unsigned k = 0; k < n; k++) {
            TRACE("linear_eq_solver", tout << "iteration " << k << "\n"; display(tout););
            // find pivot 
            unsigned i = k;
            for (; i < n; i++) {
                if (!m.is_zero(A[i][k]))
                    break;
            }
            if (i == n)
                return false; // matrix is singular
            A[k].swap(A[i]); // swap rows
            svector<numeral> & A_k = A[k];
            numeral & A_k_k = A_k[k];
            SASSERT(!m.is_zero(A_k_k));
            // normalize row
            for (unsigned i = k+1; i < n; i++) 
                m.div(A_k[i], A_k_k, A_k[i]); 
            m.div(b[k], A_k_k, b[k]);
            m.set(A_k_k, 1);
            // check if first k-1 positions are zero
            DEBUG_CODE({ for (unsigned i = 0; i < k; i++) { SASSERT(m.is_zero(A_k[i])); } });
            // for all rows below pivot
            for (unsigned i = k+1; i < n; i++) {
                svector<numeral> & A_i = A[i];
                numeral & A_i_k = A_i[k];
                for (unsigned j = k+1; j < n; j++) {
                    m.submul(A_i[j], A_i_k, A_k[j], A_i[j]);
                }
                m.submul(b[i], A_i_k, b[k], b[i]);
                m.set(A_i_k, 0);
            }
        }
        unsigned k = n;
        while (k > 0) {
            --k;
            TRACE("linear_eq_solver", tout << "iteration " << k << "\n"; display(tout););
            SASSERT(m.is_one(A[k][k]));
            // save result
            m.set(xs[k], b[k]);
            // back substitute
            unsigned i = k;
            while (i > 0) {
                --i;
                m.submul(b[i], A[i][k], b[k], b[i]);
                m.set(A[i][k], 0);
            }
        }
        return true;
    }

    void display(std::ostream & out) const {
        for (unsigned i = 0; i < A.size(); i++) {
            SASSERT(A[i].size() == n);
            for (unsigned j = 0; j < n; j++) {
                m.display(out, A[i][j]);
                out << " ";
            }
            m.display(out, b[i]); out << "\n";
        }
    }
};


#endif
