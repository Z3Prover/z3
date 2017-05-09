/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/

#pragma once
#include "util/vector.h"
#include <set>
#include <unordered_map>
#include <utility>
#include "util/lp/sparse_vector.h"
#include "util/lp/indexed_vector.h"
#include "util/lp/permutation_matrix.h"
#include "util/lp/linear_combination_iterator.h"
#include <stack>
namespace lean {

struct column_cell {
    unsigned m_i; // points to the row
    unsigned m_offset;  // the offset of the element in the matrix row
    column_cell(unsigned i, unsigned offset) : m_i(i), m_offset(offset) {
    }
};

template <typename T>
struct row_cell {
    unsigned m_j; // points to the column
    unsigned m_offset; // offset in column
    row_cell(unsigned j, unsigned offset, T const & val) : m_j(j), m_offset(offset), m_value(val) {
    }
    const T & get_val() const { return m_value;}
    T & get_val() { return m_value;}
    void set_val(const T& v) { m_value = v;  }
    T m_value;
};

// each assignment for this matrix should be issued only once!!!
template <typename T, typename X>
class static_matrix
#ifdef LEAN_DEBUG
    : public matrix<T, X>
#endif
{
    struct dim {
        unsigned m_m;
        unsigned m_n;
        dim(unsigned m, unsigned n) :m_m(m), m_n(n) {}
    };
    std::stack<dim> m_stack;
	vector<unsigned> m_became_zeros; // the row indices that became zeroes during the pivoting
public:
    typedef vector<row_cell<T>> row_strip;
    typedef vector<column_cell> column_strip;
    vector<int> m_vector_of_row_offsets;
    indexed_vector<T> m_work_vector;
    vector<row_strip> m_rows;
    vector<column_strip> m_columns;
    // starting inner classes
    class ref {
        static_matrix & m_matrix;
        unsigned m_row;
        unsigned m_col;
    public:
        ref(static_matrix & m, unsigned row, unsigned col):m_matrix(m), m_row(row), m_col(col) {}
        ref & operator=(T const & v) { m_matrix.set( m_row, m_col, v); return *this; }

        ref & operator=(ref const & v) { m_matrix.set(m_row, m_col, v.m_matrix.get(v.m_row, v.m_col)); return *this; }

        operator T () const { return m_matrix.get_elem(m_row, m_col); }
    };

    class ref_row {
        static_matrix & m_matrix;
        unsigned        m_row;
    public:
        ref_row(static_matrix & m, unsigned row):m_matrix(m), m_row(row) {}
        ref operator[](unsigned col) const { return ref(m_matrix, m_row, col); }
    };

public:

    const T & get_val(const column_cell & c) const {
        return m_rows[c.m_i][c.m_offset].get_val();
    }
    
    void init_row_columns(unsigned m, unsigned n);

        // constructor with no parameters
    static_matrix() {}

    // constructor
    static_matrix(unsigned m, unsigned n): m_vector_of_row_offsets(n, -1)  {
        init_row_columns(m, n);
    }
    // constructor that copies columns of the basis from A
    static_matrix(static_matrix const &A, unsigned * basis);

    void clear();

    void init_vector_of_row_offsets();

    void init_empty_matrix(unsigned m, unsigned n);

    unsigned row_count() const { return static_cast<unsigned>(m_rows.size()); }

    unsigned column_count() const { return static_cast<unsigned>(m_columns.size()); }

    unsigned lowest_row_in_column(unsigned col);

    void add_columns_at_the_end(unsigned delta);
    void add_new_element(unsigned i, unsigned j, const T & v);

    void add_row() {m_rows.push_back(row_strip());}
    void add_column() {
        m_columns.push_back(column_strip());
        m_vector_of_row_offsets.push_back(-1);
    }

    void forget_last_columns(unsigned how_many_to_forget);

    void remove_last_column(unsigned j);

    void remove_element(vector<row_cell<T>> & row, row_cell<T> & elem_to_remove);
    
    void multiply_column(unsigned column, T const & alpha) {
        for (auto & t : m_columns[column]) {
            auto & r = m_rows[t.m_i][t.m_offset];
            r.m_value *= alpha;
        }
    }
    

#ifdef LEAN_DEBUG
    void regen_domain();
#endif

    // offs - offset in columns
    row_cell<T> make_row_cell(unsigned row, unsigned offs, T const & val) {
        return row_cell<T>(row, offs, val);
    }

    column_cell make_column_cell(unsigned column, unsigned offset) {
        return column_cell(column, offset);
    }

    void set(unsigned row, unsigned col, T const & val);

    ref operator()(unsigned row, unsigned col) { return ref(*this, row, col); }

    std::set<std::pair<unsigned, unsigned>>  get_domain();

    void copy_column_to_indexed_vector(unsigned j, indexed_vector<T> & v) const;

    T get_max_abs_in_row(unsigned row) const;
    void add_column_to_vector (const T & a, unsigned j, T * v) const {
        for (const auto & it : m_columns[j]) {
            v[it.m_i] += a * get_val(it);
        }
    }

    T get_min_abs_in_row(unsigned row) const;
    T get_max_abs_in_column(unsigned column) const;

    T get_min_abs_in_column(unsigned column) const;

#ifdef LEAN_DEBUG
    void check_consistency();
#endif


    void cross_out_row(unsigned k);

    //
    void fix_row_indices_in_each_column_for_crossed_row(unsigned k);

    void cross_out_row_from_columns(unsigned k, row_strip & row);

    void cross_out_row_from_column(unsigned col, unsigned k);

    T get_elem(unsigned i, unsigned j) const;


    unsigned number_of_non_zeroes_in_column(unsigned j) const { return m_columns[j].size(); }

    unsigned number_of_non_zeroes_in_row(unsigned i) const { return m_rows[i].size(); }

    unsigned number_of_non_zeroes() const {
        unsigned ret = 0;
        for (unsigned i = 0; i < row_count(); i++)
            ret += number_of_non_zeroes_in_row(i);
        return ret;
    }
    
    void scan_row_to_work_vector(unsigned i);

    void clean_row_work_vector(unsigned i);


#ifdef LEAN_DEBUG
    unsigned get_number_of_rows() const { return row_count(); }
    unsigned get_number_of_columns() const { return column_count(); }
    virtual void set_number_of_rows(unsigned /*m*/) { }
    virtual void set_number_of_columns(unsigned /*n*/) { }
#endif

    T get_max_val_in_row(unsigned /* i */) const { lean_unreachable();   }

    T get_balance() const;

    T get_row_balance(unsigned row) const;

    bool is_correct() const;
    void push() {
        dim d(row_count(), column_count());
        m_stack.push(d);
    }

    void pop_row_columns(const vector<row_cell<T>> & row) {
        for (auto & c : row) {
            unsigned j = c.m_j;
            auto & col = m_columns[j];
            lean_assert(col[col.size() - 1].m_i == m_rows.size() -1 ); // todo : start here!!!!
            col.pop_back();
        }
    }

    
    
    void pop(unsigned k) {
#ifdef LEAN_DEBUG
        std::set<std::pair<unsigned, unsigned>> pairs_to_remove_from_domain;
#endif
        
        
        while (k-- > 0) {
            if (m_stack.empty()) break;
            unsigned m = m_stack.top().m_m;
            while (m < row_count()) {
                unsigned i = m_rows.size() -1 ;
                auto & row = m_rows[i];
                pop_row_columns(row);
                m_rows.pop_back(); // delete the last row
            }
            unsigned n = m_stack.top().m_n;
            while (n < column_count())
                m_columns.pop_back(); // delete the last column
            m_stack.pop();
        }
        lean_assert(is_correct());
    }

    void multiply_row(unsigned row, T const & alpha) {
        for (auto & t : m_rows[row]) {
            t.m_value *= alpha;
        }
    }

    void divide_row(unsigned row, T const & alpha) {
        for (auto & t : m_rows[row]) {
            t.m_value /= alpha;
        }
    }
    
    T dot_product_with_column(const vector<T> & y, unsigned j) const {
        lean_assert(j < column_count());
        T ret = numeric_traits<T>::zero();
        for (auto & it : m_columns[j]) {
            ret += y[it.m_i] * get_val(it); // get_value_of_column_cell(it);
        }
        return ret;
    }

    // pivot row i to row ii
    bool pivot_row_to_row_given_cell(unsigned i, column_cell& c, unsigned);
    void scan_row_ii_to_offset_vector(unsigned ii);

    void transpose_rows(unsigned i, unsigned ii) {
        auto t = m_rows[i];
        m_rows[i] = m_rows[ii];
        m_rows[ii] = t;
        // now fix the columns
        for (auto & rc : m_rows[i]) {
            column_cell & cc = m_columns[rc.m_j][rc.m_offset];
            lean_assert(cc.m_i == ii);
            cc.m_i = i;
        }
        for (auto & rc : m_rows[ii]) {
            column_cell & cc = m_columns[rc.m_j][rc.m_offset];
            lean_assert(cc.m_i == i);
            cc.m_i = ii;
        }
    
    }

    void fill_last_row_with_pivoting(linear_combination_iterator<T> & it, const vector<int> & basis_heading) {
        lean_assert(numeric_traits<T>::precise());
        lean_assert(row_count() > 0);
        m_work_vector.resize(column_count());
        T a;
        unsigned j;
        while (it.next(a, j)) {
            m_work_vector.set_value(-a, j); // we use the form -it + 1 = 0
            // but take care of the basis 1 later
        }
    
        it.reset();
        // not iterate with pivoting
        while (it.next(j)) {
            int row_index = basis_heading[j];
            if (row_index < 0)
                continue;

            T & alpha = m_work_vector[j]; // the pivot alpha
            if (is_zero(alpha))
                continue;
        
            for (const auto & c : m_rows[row_index]) {
                if (c.m_j == j) {
                    continue;
                }
                T & wv = m_work_vector.m_data[c.m_j];
                bool was_zero = is_zero(wv);
                wv -= alpha * c.m_value;
                if (was_zero)
                    m_work_vector.m_index.push_back(c.m_j);
                else {
                    if (is_zero(wv)) {
                        m_work_vector.erase_from_index(c.m_j);
                    }
                }
            }
            alpha = zero_of_type<T>();
            m_work_vector.erase_from_index(j);
        }
        lean_assert(m_work_vector.is_OK());
        unsigned last_row = row_count() - 1;
    
        for (unsigned j : m_work_vector.m_index) {
            set (last_row, j, m_work_vector.m_data[j]);
        }
        lean_assert(column_count() > 0);
        set(last_row, column_count() - 1, one_of_type<T>());
    }

    void copy_column_to_vector (unsigned j, vector<T> & v) const {
        v.resize(row_count(), numeric_traits<T>::zero());
        for (auto & it : m_columns[j]) {
            const T& val = get_val(it);
            if (!is_zero(val))
                v[it.m_i] = val;
        }
    }
    
    template <typename L>
    L dot_product_with_row(unsigned row, const vector<L> & w) const {
        L ret = zero_of_type<L>();
        lean_assert(row < m_rows.size());
        for (auto & it : m_rows[row]) {
            ret += w[it.m_j] * it.get_val();
        }
        return ret;
    }
};
}
