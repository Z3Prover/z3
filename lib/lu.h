/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    lu.h

Abstract:

    Simple LU factorization module based on the paper:
    
    "Maintaining LU factors of a General Sparse Matrix"
    P. E. Gill, W. Murray, M. Saunders, M. Wright

Author:

    Leonardo de Moura (leonardo) 2011-06-09

Revision History:

--*/
#ifndef _LU_H_
#define _LU_H_

#include"vector.h"
#include"mpq.h"
#include"double_manager.h"
#include"permutation.h"
#include"params.h"
#include"strategy_exception.h"

MK_ST_EXCEPTION(lu_exception);

template<typename NumManager>
class lu {
public:
    typedef NumManager manager;
    typedef typename NumManager::numeral numeral;
    typedef svector<numeral> numeral_vector;

private:
    manager &        m_manager;
    
    // Configuration
    numeral          m_mu;  // maximum multiplier when selecting a pivot
    unsigned         m_selection_cutoff;
    
    // Matrix size
    unsigned         m_sz; // supporting only square matrices

    // Permutations
    permutation      P;  
    permutation      Q;
    
    // L 
    //
    // It is 3 parallel vectors representing the sequence (product) of matrices
    //            L[0] L[1] ... L[m-1]
    // where each L[i] is a tuple (A[i], indc[i], indr[i]).
    // Each tuple represents a triangular factor. That is, an identity matrix
    // where the position at row indc[i], and column indr[i] contains the value A[i].
    // Remark: The product L[0] L[1] ... L[n-1] is not really a triangular matrix.
    struct L_file {
        numeral_vector   A;
        unsigned_vector  indc;
        unsigned_vector  indr;
    };
    L_file L;
    

    // U
    //
    // It is not really upper triangular, but the product PUQ is.
    // The rows of U are stored in the parallel vectors (A, indr)
    // Only the non-zero values are stored at U.
    // The non-zeros of row i start at position begr[i] and end at 
    // position endr[i] of the parallel vectors (A, indr). 
    // The length of the row is endr[i] - begr[i].
    // The coefficients are stored in A, and the column ids at indr.
    //
    // The factorization of a matrix A is represented as:
    //    L[0] L[1] ... L[m-1] P U Q
    struct U_file {
        numeral_vector  A;
        unsigned_vector indr;
        unsigned_vector begr;
        unsigned_vector endr;
        
        unsigned num_entries;
        U_file():num_entries(0) {}
    };
    U_file U;
    
    // The actual factorization

    
    // T_file: temporary file used for factorization
    struct T_file {
        // row list
        unsigned_vector indr;
        unsigned_vector begr;
        unsigned_vector endr;
        
        // column list
        numeral_vector  A;
        unsigned_vector indc;
        unsigned_vector begc;
        unsigned_vector endc;

        unsigned        num_entries;
        T_file():num_entries(0) {}
    };
    T_file T;
    
    // Auxiliary fields
    unsigned_vector locw;
    
    // -----------------------
    //
    // Main
    //
    // -----------------------
public:
    lu(manager & m, params_ref const & p);
    ~lu();

    manager & m() const { return m_manager; }

    void updt_params(params_ref const & p);

    void reset();

    unsigned size() const { return m_sz; }

protected:
    void del_nums(numeral_vector & nums);

    // -----------------------
    //
    // Initialization
    //
    // -----------------------
public:
    // Contract for setting up the initial matrix:
    //   lu.init(size)
    //   - for each row r in the matrix
    //     - for each non-zero (a,x) in the row
    //        lu.add_entry(a, x)
    //     lu.end_row()
    void init(unsigned size);
    void add_entry(numeral const & a, unsigned x);
    void end_row();

protected:
    // auxiliary fields used during initialization
    bool     ini; // try if the matrix T is being setup using the protocol above
    unsigned ini_irow;
    unsigned fillin_for(unsigned sz);
    void move_col_to_end(unsigned x);
    void move_row_to_end(unsigned x);

    // -----------------------
    //
    // Factorization
    //
    // -----------------------
public:
    void fact();

protected:
    class todo {
        unsigned_vector          m_elem2len;
        unsigned_vector          m_elem2pos;
        vector<unsigned_vector>  m_elems_per_len;
        unsigned                 m_size;
    public:
        todo():m_size(0) {}
        bool contains(unsigned elem) const { return m_elem2pos[elem] != UINT_MAX; }
        void init(unsigned capacity);
        void updt_len(unsigned elem, unsigned len);
        unsigned len(unsigned elem) const { return m_elem2len[elem]; }
        void erase(unsigned elem);
        unsigned size() const { return m_size; }
        void display(std::ostream & out) const;
        class iterator {
            todo const & m_todo;
            unsigned     m_i;
            unsigned     m_j;
            unsigned     m_c;
            void find_next();
        public:
            iterator(todo const & t):m_todo(t), m_i(0), m_j(0), m_c(0) { if (!at_end()) find_next(); }
            bool at_end() const { return m_c == m_todo.m_size; }
            unsigned curr() const { 
                unsigned_vector const & v_i = m_todo.m_elems_per_len[m_i];
                return v_i[m_j]; 
            }
            void next() { SASSERT(!at_end()); m_j++; m_c++; find_next(); }
        };
    };

    todo          m_todo_rows;
    todo          m_todo_cols;
    svector<bool> m_enabled_rows;
    svector<bool> m_enabled_cols;

    bool enabled_row(unsigned r) const { return m_enabled_rows[r]; }
    bool enabled_col(unsigned c) const { return m_enabled_cols[c]; }

    unsigned_vector m_toadd_rows;
    svector<bool>   m_marked_rows;

    // Temporary numerals
    // I do not use local numerals to avoid memory leaks
    numeral         tol;
    numeral         C_max;
    numeral         A_ij;
    numeral         A_best;
    numeral         A_aux;
    numeral         tmp;
    numeral         mu_best;
    numeral         mu_1;

    void init_fact();
    bool stability_test(unsigned rin, unsigned cin, bool improvingM);
    void select_pivot(unsigned & r_out, unsigned & c_out);
    void process_pivot_core(unsigned r, unsigned c);
    void process_pivot(unsigned i, unsigned r, unsigned c);
    bool check_locw() const;
    void dec_lenr(unsigned r);
    void inc_lenr(unsigned r);
    void dec_lenc(unsigned c);
    void inc_lenc(unsigned c);
    void del_row_entry(unsigned r, unsigned c);
    void del_disabled_cols(unsigned r);
    void add_row_entry(unsigned r, unsigned c);
    void add_col_entry(unsigned r, unsigned c, numeral const & a);
    void compress_rows();
    void compress_columns();
    void compress_if_needed();
    void copy_T_to_U();

    bool check_lenr() const;
    bool check_lenc() const;

    // -----------------------
    //
    // Solving
    //
    // -----------------------
public:
    
    // Temporary vector used to interact with different solvers.
    // The vector has support for tracking non-zeros.
    class dense_vector {
    public:
        typedef typename lu<NumManager>::manager manager;
        typedef typename lu<NumManager>::numeral numeral;
    private:
        friend class lu;
        manager &       m_manager;
        unsigned_vector m_non_zeros; // positions that may contain non-zeros. if a position is not here, then it must contain a zero
        char_vector     m_in_non_zeros; // m_in_non_zeros[i] == true if m_non_zeros contains i.
        numeral_vector  m_values;
    public:
        dense_vector(manager & m, unsigned sz);
        ~dense_vector();

        manager & m() const { return m_manager; }
        
        void reset();
        void reset(unsigned new_sz);
        
        unsigned size() const { return m_values.size(); }
        numeral const & operator[](unsigned idx) const { return m_values[idx]; }
        
        void swap(dense_vector & other) {
            m_non_zeros.swap(other.m_non_zeros);
            m_in_non_zeros.swap(other.m_in_non_zeros);
            m_values.swap(other.m_values);
        }

        // Get a given position for performing an update.
        // idx is inserted into m_non_zeros.
        numeral & get(unsigned idx) {
            if (!m_in_non_zeros[idx]) {
                m_in_non_zeros[idx] = true;
                m_non_zeros.push_back(idx);
            }
            return m_values[idx];
        }
        
        typedef unsigned_vector::const_iterator iterator;
        
        // iterator for positions that may contain non-zeros
        iterator begin_non_zeros() const { return m_non_zeros.begin(); }
        iterator end_non_zeros() const { return m_non_zeros.end(); }
        
        void display(std::ostream & out) const;
        void display_non_zeros(std::ostream & out) const;
        void display_pol(std::ostream & out) const;

        void elim_zeros();
    };

    // Solve: Lx = y
    // The result is stored in y.
    void solve_Lx_eq_y(dense_vector & y);
    
    // Solve: PUQx = y  
    // The result is stored in y.
    void solve_Ux_eq_y(dense_vector & y);
    
    // Solve: LPUQx = y
    // The result is stored in y.
    void solve_Ax_eq_y(dense_vector & y) {
        solve_Lx_eq_y(y); 
        solve_Ux_eq_y(y);
    }

    // Solve: xL = y
    // The result is stored in y.
    void solve_xL_eq_y(dense_vector & y);
    
    // Solve: xPUQ = y
    // The result is stored in y.
    void solve_xU_eq_y(dense_vector & y);

    // Solve: xA = y
    // The result is stored in y.
    void solve_xA_eq_y(dense_vector & y) {
        solve_xU_eq_y(y);
        solve_xL_eq_y(y);
    }

private:
    dense_vector m_tmp_xU_vector;
    dense_vector m_tmp_replace_column_vector;
    dense_vector m_tmp_vector;
    dense_vector m_tmp_row;

public:
    dense_vector & get_tmp_vector() { return m_tmp_vector; }
    dense_vector & get_tmp_row(unsigned size) { m_tmp_row.reset(size); return m_tmp_row; }

    // -----------------------
    //
    // Column replacement
    //
    // -----------------------
public:
    void replace_column(unsigned j, dense_vector & new_col);
    void replace_U_column(unsigned j, dense_vector & new_col);
    unsigned get_num_replacements() const { return m_num_replacements; }
    dense_vector & get_tmp_col() { return m_tmp_col; }

private:
    unsigned        m_num_replacements;
    dense_vector    m_tmp_col;

    void del_U_row_entry(unsigned r, unsigned c);
    void compress_U_rows();
    void compress_U_if_needed();
    void move_U_row_to_end(unsigned r);
    void add_U_row_entry(unsigned r, unsigned c, numeral const & a);
    void add_replace_U_row_entry(unsigned r, unsigned c, numeral const & a);
    unsigned replace_U_column_core(unsigned j, dense_vector & new_col);
    bool check_U_except_col(unsigned c) const;
    bool check_U_except_row(unsigned r) const;
    
    // -----------------------
    //
    // Invariants
    //
    // -----------------------
public:
    bool check_P() const;    
    bool check_Q() const;    
    bool check_L() const;
    bool check_U() const;
    bool T_col_contains(unsigned c, unsigned r) const;
    bool T_row_contains(unsigned r, unsigned c) const;
    bool check_T() const;
    bool check_invariant() const;

    void display_T(std::ostream & out) const;
    void display_U(std::ostream & out, unsigned_vector const * var_ids = 0) const;
    void display_L(std::ostream & out) const;
    void display(std::ostream & out, unsigned_vector const * var_ids = 0) const;

    // -----------------------
    //
    // Info
    //
    // -----------------------
public:
    unsigned L_size() const { return L.indc.size(); }
    unsigned U_size() const { return U.num_entries; }
};

typedef lu<unsynch_mpq_manager> rational_lu;
typedef lu<double_manager>      double_lu;

#endif
