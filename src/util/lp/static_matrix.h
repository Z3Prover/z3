/*++
  Copyright (c) 2017 Microsoft Corporation

  Module Name:

  <name>

  Abstract:

  <abstract>

  Author:

  Lev Nachmanson (levnach)

  Revision History:


  --*/

#pragma once
#include "util/vector.h"
#include <set>
#include <unordered_map>
#include <utility>
#include "util/lp/sparse_vector.h"
#include "util/lp/indexed_vector.h"
#include "util/lp/permutation_matrix.h"
#include <stack>
namespace lp {

class column_cell {
    unsigned  m_i; // points to the row
    unsigned  m_offset;  // the offset of the element in the matrix row, or the next dead cell in the column_strip
public:
    column_cell(unsigned  i, unsigned  offset) : m_i(i), m_offset(offset) { }
    column_cell(unsigned  i) : m_i(i) { }

    // index of of the cell row
    unsigned  var() const {
        lp_assert(alive());
        return m_i;
    }
    unsigned  &var() {
        return m_i;
    }
    unsigned  offset() const {
        lp_assert(alive());
        return m_offset;
    }
    unsigned  & offset() {
        lp_assert(alive());
        return m_offset;
    }

    unsigned next_dead_index() const {
        lp_assert(dead());
        return m_offset;
    }
    unsigned & next_dead_index() {
        return m_offset;
    }
    
    bool alive() const { return !dead(); }
    bool dead() const { return m_i == static_cast<unsigned>(-1); }
    void set_dead() { m_i = -1;}



};

template <typename T>
class row_cell {
    unsigned  m_j; // points to the column
    unsigned  m_offset; // offset in column, or the next dead cell in the row_strip
    T              m_value;
public:
    row_cell(unsigned j, unsigned offset, T const & val) : m_j(j), m_offset(offset), m_value(val) {
    }
    row_cell(unsigned j, T const & val) : m_j(j), m_value(val) {
    }
    const T & get_val() const {
        lp_assert(alive());
        return m_value;
    }
    T & get_val() { 
        lp_assert(alive());
        return m_value;
    }
    void set_val(const T& v) {
        lp_assert(alive());
        m_value = v;
    }
    // index of the cell column
    unsigned var() const {
        lp_assert(alive());
        return m_j;
    }
    unsigned  &var() {         
        return m_j;
    }
    const T & coeff() const {
        lp_assert(alive());
        return m_value;
    }
    T & coeff() {
        lp_assert(alive());
        return m_value;
    }
    // offset in the column vector
    unsigned  offset() const {
        lp_assert(alive());
        return m_offset;
    }
    unsigned  & offset() {
        return m_offset;
    }
    unsigned next_dead_index() const {
        lp_assert(dead());
        return m_offset;
    }
    unsigned & next_dead_index() {
        lp_assert(dead());
        return m_offset;
    }
    bool alive() const { return !dead(); }
    bool dead() const { return m_j == static_cast<unsigned>(-1); }
    void set_dead() { m_j = static_cast<unsigned>(-1); }


};

template <typename T>
class row_strip {
    unsigned m_live_size;
    int      m_first_dead;
public:    
    row_strip() : m_live_size(0), m_first_dead(-1) {}
    row_cell<T>* begin() { return m_cells.begin();}
    const row_cell<T>* begin() const { return m_cells.begin();}
    row_cell<T>* end() { return m_cells.end();}
    const row_cell<T>* end() const { return m_cells.end();}
    unsigned live_size() const { return m_live_size; } 
    vector<row_cell<T>> m_cells;
    unsigned cells_size() const { return m_cells.size(); }
    const row_cell<T> & operator[](unsigned i) const { return m_cells[i]; }
    row_cell<T> & operator[](unsigned i) { return m_cells[i];}

    void skip_dead_cell(unsigned k) {
        lp_assert(m_cells[k].dead())
        auto * c = &m_cells[m_first_dead];
        for (; c->next_dead_index() != k; c = &m_cells[c->next_dead_index()]);
        lp_assert(c->next_dead_index() == k);
        c->next_dead_index() = m_cells[k].next_dead_index();
    }

    void pop_last_dead_cell() {
        lp_assert(m_cells.back().dead());
        unsigned last = m_cells.size() - 1;
        if (m_first_dead == static_cast<int>(last)) 
            m_first_dead = m_cells.back().next_dead_index();
        else {
            skip_dead_cell(last);
        }
        m_cells.pop_back();
    }

    void pop(){
        bool dead = m_cells.back().dead();
        if (dead) {
            pop_last_dead_cell();
        } else {
            m_live_size --;
            m_cells.pop_back();
        }
    }
    
    bool empty() const { return m_live_size == 0; }

    void delete_at(unsigned j) {
        lp_assert(m_cells[j].alive());
        m_live_size--;
        if (j == m_cells.size() - 1)
            m_cells.pop_back();
        else {
            auto & c = m_cells[j];
            c.set_dead();
            c.next_dead_index() = m_first_dead;
            m_first_dead = j;
        }
        lp_assert(is_correct());
    }

    bool is_correct() const {
        std::set<unsigned> d0;
        std::set<unsigned> d1;
        unsigned alive = 0;
        for (unsigned i = 0; i < m_cells.size(); i++) {
            if (m_cells[i].dead())
                d0.insert(i);
            else
                alive ++;
        }

        if ( alive != m_live_size)
            return false;
        
        for (unsigned i = m_first_dead; i != static_cast<unsigned>(-1) ; i = m_cells[i].next_dead_index())
            d1.insert(i);
        return d0 == d1;
    }

    row_cell<T> & add_cell(unsigned j, const T& val, unsigned & index) {
#ifdef Z3DEBUG
        for (const auto & c : m_cells) {
            if (c.dead()) continue;
            if (c.var() == j)
                std::cout << "oops" << std::endl;
        }
#endif
        if (m_first_dead != -1) {
            auto & ret = m_cells[index = m_first_dead];
            m_first_dead = ret.next_dead_index();
            m_live_size++;
            ret.var() = j;
            ret.coeff() = val;
            return ret;
        }
        lp_assert(m_live_size == m_cells.size());
        index = m_live_size++;
        m_cells.push_back(row_cell<T>(j, val));
        return m_cells.back();
    }

    void shrink_to_live() {
        m_cells.shrink(live_size());
        m_first_dead = -1;
    }
};

class column_strip {
    vector<column_cell> m_cells;
    unsigned            m_live_size;
    int                 m_first_dead;
public:
    column_strip() : m_live_size(0), m_first_dead(-1) { }
    column_cell* begin() { return m_cells.begin();}
    const column_cell* begin() const { return m_cells.begin();}
    column_cell* end() { return m_cells.end();}
    const column_cell* end() const { return m_cells.end();}
    unsigned live_size() const {
        return m_live_size;
    }

    unsigned cells_size() const {
        return m_cells.size();
    }

    unsigned cells_size() const {
        return m_cells.size();
    }
    
    column_cell& back() { return m_cells.back(); }
    void delete_at(unsigned j) {
        lp_assert(m_cells[j].alive());
        m_live_size--;
        if (j == m_cells.size() - 1)
            m_cells.pop_back();
        else {
            auto & c = m_cells[j];
            c.set_dead();
            c.next_dead_index() = m_first_dead;
            m_first_dead = j;
        }
        lp_assert(is_correct());
    }
    
    const column_cell& operator[] (unsigned i) const { return m_cells[i];}
    column_cell& operator[](unsigned i) { return m_cells[i];}
    void pop() {
        bool dead = m_cells.back().dead();
        if (dead) {
            pop_last_dead_cell();
        } else {
            m_live_size --;
            m_cells.pop_back();
        }
    }
    void skip_dead_cell(unsigned k) {
        lp_assert(m_cells[k].dead())
        auto * c = &m_cells[m_first_dead];
        for (; c->next_dead_index() != k; c = &m_cells[c->next_dead_index()]);
        lp_assert(c->next_dead_index() == k);
        c->next_dead_index() = m_cells[k].next_dead_index();
    }
    
    void pop_last_dead_cell() {
        lp_assert(m_cells.back().dead());
        unsigned last = m_cells.size() - 1;
        if (m_first_dead == static_cast<int>(last)) 
            m_first_dead = m_cells.back().next_dead_index();
        else {
            skip_dead_cell(last);
        }
        m_cells.pop_back();
    }

        std::set<unsigned> d0;
        std::set<unsigned> d1;
        unsigned alive = 0;
        for (unsigned i = 0; i < m_cells.size(); i++) {
            if (m_cells[i].dead())
                d0.insert(i);
            else
                alive ++;
        }

        if (alive != m_live_size)
            return false;
        for (unsigned i = m_first_dead; i != static_cast<unsigned>(-1) ; i = m_cells[i].next_dead_index())
            d1.insert(i);
        return d0 == d1;
    }

    void swap_with_head_cell(unsigned i) {
        lp_assert(i > 0);
        lp_assert(m_cells[i].alive());
        column_cell head_copy = m_cells[0];
        if (head_copy.dead()) {
            if (m_first_dead == 0) {
                m_first_dead = i;
            } else {
                column_cell * c = &m_cells[m_first_dead];
                for (; c->next_dead_index() != 0; c = &m_cells[c->next_dead_index()]);
                lp_assert(c->next_dead_index() == 0);
                c->next_dead_index() = i;
            }
        }
        m_cells[0] = m_cells[i];
        m_cells[i] = head_copy;
        lp_assert(is_correct());
    }

    void swap_with_head_cell(unsigned i) {
        lp_assert(i > 0);
        lp_assert(m_cells[i].alive());
        column_cell head_copy = m_cells[0];
        if (head_copy.dead()) {
            if (m_first_dead == 0) {
                m_first_dead = i;
            } else {
                column_cell * c = &m_cells[m_first_dead];
                for (; c->next_dead_index() != 0; c = &m_cells[c->next_dead_index()]);
                lp_assert(c->next_dead_index() == 0);
                c->next_dead_index() = i;
            }
        }
        m_cells[0] = m_cells[i];
        m_cells[i] = head_copy;
        lp_assert(is_correct());
    }

    column_cell & add_cell(unsigned i, unsigned & index) {
        if (m_first_dead != -1) {
            auto & ret = m_cells[index = m_first_dead];
            m_first_dead = ret.next_dead_index();
            m_live_size++;
            ret.var() = i;
            return ret;
        }
        lp_assert(m_live_size == m_cells.size());
        index = m_live_size++;
        m_cells.push_back(column_cell(i));
        return m_cells.back();
    }
    column_cell & add_cell(unsigned i, unsigned & index) {
        if (m_first_dead != -1) {
            auto & ret = m_cells[index = m_first_dead];
            m_first_dead = ret.next_dead_index();
            m_live_size++;
            ret.var() = i;
            return ret;
        }
        lp_assert(m_live_size == m_cells.size());
        index = m_live_size++;
        m_cells.push_back(column_cell(i));
        return m_cells.back();
    }
    void shrink_to_live() {
        m_cells.shrink(live_size());
        m_first_dead = -1;
    }
};

template <typename A, typename B>
void compress_cells(A& cells, vector<B>& vec_of_cells) {
    if (2 * cells.live_size() < cells.cells_size())
        return;
    unsigned j = 0; // the available target for copy
    for (unsigned i = 0; i < cells.cells_size(); i++) {
        auto & c = cells[i];
        if (c.dead()) continue;
        if (i == j) {
            j++;
            continue;
        }
        vec_of_cells[c.var()][c.offset()].offset() = j;
        cells[j++] = c;
    }
    cells.shrink_to_live();
}


// each assignment for this matrix should be issued only once!!!
template <typename T, typename X>
class static_matrix
#ifdef Z3DEBUG
    : public matrix<T, X>
#endif
{
    struct dim {
        unsigned m_m;
        unsigned m_n;
        dim(unsigned m, unsigned n) :m_m(m), m_n(n) {}
    };
    // fields
    std::stack<dim>          m_stack;
public:
    vector<int>              m_vector_of_row_offsets;
    indexed_vector<T>        m_work_vector;
    vector<row_strip<T>>     m_rows;
    vector<column_strip>     m_columns;
    // starting inner classes
    class ref {
        static_matrix & m_matrix;
        unsigned m_row;
        unsigned m_col;
    public:
        ref(static_matrix & m, unsigned row, unsigned col):m_matrix(m), m_row(row), m_col(col) {}
        ref & operator=(T const & v) { m_matrix.add_new_element( m_row, m_col, v); return *this; }

        ref operator=(ref & v) { m_matrix.add_new_element(m_row, m_col, v.m_matrix.get(v.m_row, v.m_col)); return *this; }

        operator T () const { return m_matrix.get_elem(m_row, m_col); }
    };

    class ref_row {
        const static_matrix & m_matrix;
        unsigned        m_row;
    public:
        ref_row(const static_matrix & m, unsigned row): m_matrix(m), m_row(row) {}
        const T operator[](unsigned col) const { return m_matrix.get_elem(m_row, col); }
    };

public:

    const T & get_val(const column_cell & c) const {
        return m_rows[c.var()][c.offset()].get_val();
    }

    column_cell & get_column_cell(const row_cell<T> &rc) {
        return m_columns[rc.m_j][rc.m_offset];
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

    void add_row() {m_rows.push_back(row_strip<T>());}
    void add_column() {
        m_columns.push_back(column_strip());
        m_vector_of_row_offsets.push_back(-1);
    }

    void forget_last_columns(unsigned how_many_to_forget);

    void remove_last_column(unsigned j);

    void remove_element(row_cell<T> & elem_to_remove);
    
    void multiply_column(unsigned column, T const & alpha) {
        for (auto & t : m_columns[column]) {
            auto & r = m_rows[t.var()].m_cells[t.offset()];
            r.coeff() *= alpha;
        }
    }
    

#ifdef Z3DEBUG
    void regen_domain();
#endif

    // offs - offset in columns
    row_cell<T> make_row_cell(unsigned row, unsigned offs, T const & val) {
        return row_cell<T>(row, offs, val);
    }

    column_cell make_column_cell(unsigned column, unsigned offset) {
        return column_cell(column, offset);
    }

    ref operator()(unsigned row, unsigned col) { return ref(*this, row, col); }

    std::set<std::pair<unsigned, unsigned>>  get_domain();

    void copy_column_to_indexed_vector(unsigned j, indexed_vector<T> & v) const;

    T get_max_abs_in_row(unsigned row) const;
    void add_column_to_vector (const T & a, unsigned j, T * v) const {
        for (const auto & c : m_columns[j]) {
            v[c.var()] += a * get_val(c);
        }
    }

    T get_min_abs_in_row(unsigned row) const;
    T get_max_abs_in_column(unsigned column) const;

    T get_min_abs_in_column(unsigned column) const;

#ifdef Z3DEBUG
    void check_consistency();
#endif

    //
    void fix_row_indices_in_each_column_for_crossed_row(unsigned k);

    void cross_out_row_from_columns(unsigned k, row_strip<T> & row);

    void cross_out_row_from_column(unsigned col, unsigned k);

    T get_elem(unsigned i, unsigned j) const;


    unsigned number_of_non_zeroes_in_column(unsigned j) const { return m_columns[j].live_size(); }

    unsigned number_of_non_zeroes_in_row(unsigned i) const { return m_rows[i].live_size(); }

    unsigned number_of_non_zeroes() const {
        unsigned ret = 0;
        for (unsigned i = 0; i < row_count(); i++)
            ret += number_of_non_zeroes_in_row(i);
        return ret;
    }
    
    void scan_row_to_work_vector(unsigned i);

    void clean_row_work_vector(unsigned i);


#ifdef Z3DEBUG
    unsigned get_number_of_rows() const { return row_count(); }
    unsigned get_number_of_columns() const { return column_count(); }
    virtual void set_number_of_rows(unsigned /*m*/) { }
    virtual void set_number_of_columns(unsigned /*n*/) { }
#endif

    T get_max_val_in_row(unsigned /* i */) const { lp_unreachable();   }

    T get_balance() const;

    T get_row_balance(unsigned row) const;

    bool is_correct() const;
    void push() {
        dim d(row_count(), column_count());
        m_stack.push(d);
    }

    void pop_row_columns(const row_strip<T> & row) {
        for (auto & c : row) {
            if (c.dead()) {
                continue;
            }
            m_columns[c.var()].delete_at(c.offset());
        }
    }

    
    
    void pop(unsigned k) {
#ifdef Z3DEBUG
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
        lp_assert(is_correct());
    }

    void multiply_row(unsigned row, T const & alpha) {
        for (auto & t : m_rows[row].m_cells) {
            if (t.alive())
                t.coeff() *= alpha;
        }
    }

    void divide_row(unsigned row, T const & alpha) {
        for (auto & t : m_rows[row]) {
            t.m_value /= alpha;
        }
    }
    
    T dot_product_with_column(const vector<T> & y, unsigned j) const {
        lp_assert(j < column_count());
        T ret = numeric_traits<T>::zero();
        for (auto & c : m_columns[j]) {
            ret += y[c.var()] * get_val(c);
        }
        return ret;
    }

    // pivot row i to row ii
    bool pivot_row_to_row_given_cell(unsigned i, column_cell& c, unsigned);
    void scan_row_ii_to_offset_vector(const row_strip<T> & rvals);

    void transpose_rows(unsigned i, unsigned ii) {
        auto t = m_rows[i];
        m_rows[i] = m_rows[ii];
        m_rows[ii] = t;
        // now fix the columns
        for (const auto & rc : m_rows[i]) {
            if (rc.dead()) continue;
            column_cell & cc = m_columns[rc.var()][rc.offset()];
            lp_assert(cc.var() == ii);
            cc.var() = i;
        }
        for (const auto & rc : m_rows[ii]) {
            if (rc.dead()) continue;
            column_cell & cc = m_columns[rc.var()][rc.offset()];
            lp_assert(cc.var() == i);
            cc.var() = ii;
        }
    }

    void fill_last_row_with_pivoting_loop_block(unsigned j, const vector<int> & basis_heading) {
        int row_index = basis_heading[j];
        if (row_index < 0)
            return;
        T & alpha = m_work_vector[j]; // the pivot alpha
        if (is_zero(alpha))
            return;
        
        for (const auto & c : m_rows[row_index]) {
            if (c.dead()) continue;
            if (c.var() == j) {
                continue;
            }
            T & wv = m_work_vector.m_data[c.var()];
            bool was_zero = is_zero(wv);
            wv -= alpha * c.coeff();
            if (was_zero)
                m_work_vector.m_index.push_back(c.var());
            else {
                if (is_zero(wv)) {
                    m_work_vector.erase_from_index(c.var());
                }
            }
        }
        alpha = zero_of_type<T>();
        m_work_vector.erase_from_index(j);
    }

    
    
    template <typename term>
    void fill_last_row_with_pivoting(const term& row,
                                     unsigned bj, // the index of the basis column
                                     const vector<int> & basis_heading) {
        lp_assert(numeric_traits<T>::precise());
        lp_assert(row_count() > 0);
        m_work_vector.resize(column_count());
        T a;
        // we use the form -it + 1 = 0
        m_work_vector.set_value(one_of_type<T>(), bj);
        for (auto p : row) {
            m_work_vector.set_value(-p.coeff(), p.var());
            // but take care of the basis 1 later
        }
    
        // now iterate with pivoting
        fill_last_row_with_pivoting_loop_block(bj, basis_heading);
        for (auto p : row) {
            fill_last_row_with_pivoting_loop_block(p.var(), basis_heading);
        }
        lp_assert(m_work_vector.is_OK());
        unsigned last_row = row_count() - 1;
    
        for (unsigned j : m_work_vector.m_index) {
            add_new_element(last_row, j, m_work_vector.m_data[j]);
        }
        lp_assert(column_count() > 0);
        add_new_element(last_row, column_count() - 1, one_of_type<T>());
    }

    void copy_column_to_vector (unsigned j, vector<T> & v) const {
        v.resize(row_count(), numeric_traits<T>::zero());
        for (auto & it : m_columns[j]) {
            const T& val = get_val(it);
            if (!is_zero(val))
                v[it.var()] = val;
        }
    }
    
    template <typename L>
    L dot_product_with_row(unsigned row, const vector<L> & w) const {
        L ret = zero_of_type<L>();
        lp_assert(row < m_rows.size());
        for (auto & it : m_rows[row]) {
            if (it.dead()) continue;
            ret += w[it.var()] * it.coeff();
        }
        return ret;
    }

    struct column_cell_plus {
        const column_cell & m_c;
        const static_matrix& m_A;
        // constructor
        column_cell_plus(const column_cell & c, const static_matrix& A) :
            m_c(c), m_A(A) {}
        unsigned var() const { return m_c.var(); }
        const T & coeff() const { return m_A.m_rows[var()][m_c.offset()].get_val(); }
        bool dead() const { return m_c.dead(); }
    };
    
    struct column_container {
        unsigned              m_j; // the column index
        const static_matrix & m_A;
        column_container(unsigned j, const static_matrix& A) : m_j(j), m_A(A) {
        }
        struct const_iterator {
            // fields
            const column_cell *m_c;
            const static_matrix& m_A;
            const column_cell *m_end;
            //typedefs
            
            
            typedef const_iterator self_type;
            typedef column_cell_plus value_type;
            typedef const column_cell_plus reference;
            //            typedef const column_cell* pointer;
            typedef int difference_type;
            typedef std::forward_iterator_tag iterator_category;

            reference operator*() const {
                return column_cell_plus(*m_c, m_A);
            }        
            self_type operator++() {  self_type i = *this;
                m_c++;
                return i;
            }

            self_type operator++(int) {
                m_c++;
                return *this;
            }

            const_iterator(const column_cell* it, const static_matrix& A) :
                m_c(it),
                m_A(A){}
            bool operator==(const self_type &other) const {
                return m_c == other.m_c;
            }
            bool operator!=(const self_type &other) const { return !(*this == other); }
        };

        const_iterator begin() const {
            return const_iterator(m_A.m_columns[m_j].begin(), m_A);
        }
        
        const_iterator end() const {
            return const_iterator(m_A.m_columns[m_j].end(), m_A);
        }
    };

    column_container column(unsigned j) const {
        return column_container(j, *this);
        
    }

    void swap_with_head_cell(unsigned j, unsigned offset) {
        column_strip & col = m_columns[j];
        column_cell & head = col[0];
        column_cell & cc   = col[offset];
        if (head.alive()) {
            m_rows[head.var()][head.offset()].offset() = offset;
        }
        lp_assert(cc.alive());
        m_rows[cc.var()][cc.offset()].offset() = 0;
        col.swap_with_head_cell(offset);
    }

    
    void compress_row_if_needed(unsigned i) {
        compress_cells(m_rows[i], m_columns);
        lp_assert(is_correct());
    }

    void compress_column_if_needed(unsigned j) {
        compress_cells(m_columns[j], m_rows);
        lp_assert(is_correct());
    }
    
    ref_row operator[](unsigned i) const { return ref_row(*this, i);}
    typedef T coefftype;
    typedef X argtype;
};

}
