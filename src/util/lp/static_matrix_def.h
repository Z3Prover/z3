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
#include "util/vector.h"
#include <utility>
#include <set>
#include "util/lp/static_matrix.h"
namespace lp {
// each assignment for this matrix should be issued only once!!!
template <typename T, typename X>
void  static_matrix<T, X>::init_row_columns(unsigned m, unsigned n) {
    lp_assert(m_rows.size() == 0 && m_columns.size() == 0);
    for (unsigned i = 0; i < m; i++){
        m_rows.push_back(row_strip<T>());
    }
    for (unsigned j = 0; j < n; j++){
        m_columns.push_back(column_strip());
    }
}


template <typename T, typename X> void static_matrix<T, X>::scan_row_ii_to_offset_vector(const row_strip<T> & rvals) {
	for (unsigned j = 0; j < rvals.cells_size(); j++) {
		if (rvals[j].dead()) continue;
		m_vector_of_row_offsets[rvals[j].var()] = j;
	}
}


template <typename T, typename X> bool static_matrix<T, X>::pivot_row_to_row_given_cell(unsigned i, column_cell & c, unsigned pivot_col) {
    lp_assert(is_correct());
    unsigned ii = c.var();
    lp_assert(i < row_count() && ii < column_count() && i != ii);
    T alpha = -get_val(c);
    lp_assert(!is_zero(alpha));
    compress_row_if_needed(ii);
    auto & rowii = m_rows[ii];
    remove_element(rowii[c.offset()]);
    scan_row_ii_to_offset_vector(rowii);
    unsigned prev_size_ii = rowii.cells_size();
    // run over the pivot row and update row ii
    for (const auto & iv : m_rows[i].m_cells) {
        if (iv.dead()) continue;
        unsigned j = iv.var();
        if (j == pivot_col) continue;
        lp_assert(!is_zero(iv.coeff()));
        T alv = alpha * iv.coeff();
        int j_offs = m_vector_of_row_offsets[j];
        if (j_offs == -1) { // it is a new element
            add_new_element(ii, j, alv);
        }
        else {
            rowii[j_offs].coeff() += alv;
        }
    }
    // clean the work vector
    for (unsigned k = 0; k < prev_size_ii; k++) {
        auto & c = rowii[k];
        if (c.dead()) continue;
        m_vector_of_row_offsets[c.var()] = -1;
    }
    // remove zeroes
    for (unsigned k = rowii.cells_size(); k-- > 0;  ) {
        auto & c = rowii[k];
        if (c.dead())
            continue;
        if (is_zero(c.coeff())) 
            remove_element(c);
    }
    lp_assert(is_correct());
    return !rowii.empty();
}


// constructor that copies columns of the basis from A
template <typename T, typename X>
static_matrix<T, X>::static_matrix(static_matrix const &A, unsigned * /* basis */) :
    m_vector_of_row_offsets(A.column_count(), numeric_traits<T>::zero()) {
    unsigned m = A.row_count();
    init_row_columns(m, m);
    while (m--) {
        for (auto & col : A.m_columns[m]){
            set(col.var(), m, A.get_value_of_column_cell(col));
        }
    }
}

template <typename T, typename X>    void static_matrix<T, X>::clear() {
    m_vector_of_row_offsets.clear();
    m_rows.clear();
    m_columns.clear();
}

template <typename T, typename X> void static_matrix<T, X>::init_vector_of_row_offsets() {
    m_vector_of_row_offsets.clear();
    m_vector_of_row_offsets.resize(column_count(), -1);
}

template <typename T, typename X>    void static_matrix<T, X>::init_empty_matrix(unsigned m, unsigned n) {
    init_vector_of_row_offsets();
    init_row_columns(m, n);
}

template <typename T, typename X> unsigned static_matrix<T, X>::lowest_row_in_column(unsigned col) {
    column_strip & colstrip = m_columns[col];
    lp_assert(colstrip.live_size() > 0);
    unsigned ret = 0;
    for (const auto & t : colstrip) {
        if (t.dead()) continue;
        if (t.var() > ret) {
            ret = t.var();
        }
    }
    return ret;
}

template <typename T, typename X>    void static_matrix<T, X>::add_columns_at_the_end(unsigned delta) {
    for (unsigned i = 0; i < delta; i++)
        add_column();
}

template <typename T, typename X>    void static_matrix<T, X>::forget_last_columns(unsigned how_many_to_forget) {
    lp_assert(m_columns.size() >= how_many_to_forget);
    unsigned j = column_count() - 1;
    for (; how_many_to_forget > 0; how_many_to_forget--) {
        remove_last_column(j --);
    }
}

template <typename T, typename X> void static_matrix<T, X>::remove_last_column(unsigned j) {
    column_strip & col = m_columns.back();
    for (auto & it : col) {
        auto & row = m_rows[it.var()];
        unsigned offset = row.size() - 1;
        for (auto row_it = row.rbegin(); row_it != row.rend(); row_it ++) {
            if (row_it->var() == j) {
                row.erase(row.begin() + offset);
                break;
            }
            offset--;
        }
    }
    m_columns.pop_back();
    m_vector_of_row_offsets.pop_back();
}

template <typename T, typename X>
std::set<std::pair<unsigned, unsigned>>  static_matrix<T, X>::get_domain() {
    std::set<std::pair<unsigned, unsigned>> ret;
    for (unsigned i = 0; i < m_rows.size(); i++) {
        for (auto &it : m_rows[i]) {
            ret.insert(std::make_pair(i, it.var()));
        }
    }
    return ret;
}


template <typename T, typename X>    void static_matrix<T, X>::copy_column_to_indexed_vector (unsigned j, indexed_vector<T> & v) const {
    lp_assert(j < m_columns.size());
    for (auto & it : m_columns[j]) {
        const T& val = get_val(it);
        if (!is_zero(val))
            v.set_value(val, it.var());
    }
}



template <typename T, typename X>    T static_matrix<T, X>::get_max_abs_in_row(unsigned row) const {
    T ret = numeric_traits<T>::zero();
    for (auto & t : m_rows[row]) {
        T a = abs(t.get_val());
        if (a  > ret) {
            ret = a;
        }
    }
    return ret;
}

template <typename T, typename X>    T static_matrix<T, X>::get_min_abs_in_row(unsigned row) const {
    bool first_time = true;
    T ret = numeric_traits<T>::zero();
    for (auto & t : m_rows[row]) {
        T a = abs(t.get_val());
        if (first_time) {
            ret = a;
            first_time = false;
        } else if (a  < ret) {
            ret = a;
        }
    }
    return ret;
}


template <typename T, typename X>    T static_matrix<T, X>::get_max_abs_in_column(unsigned column) const {
    T ret = numeric_traits<T>::zero();
    for (const auto & t : m_columns[column]) {
        T a = abs(get_val(t));
        if (a  > ret) {
            ret = a;
        }
    }
    return ret;
}

template <typename T, typename X>     T static_matrix<T, X>::get_min_abs_in_column(unsigned column) const {
    bool first_time = true;
    T ret = numeric_traits<T>::zero();
    for (auto & t : m_columns[column]) {
        T a = abs(get_val(t));
        if (first_time) {
            first_time = false;
            ret = a;
        } else if (a  < ret) {
            ret = a;
        }
    }
    return ret;
}

#ifdef Z3DEBUG
template <typename T, typename X>    void static_matrix<T, X>::check_consistency() {
    std::unordered_map<std::pair<unsigned, unsigned>, T> by_rows;
    for (int i = 0; i < m_rows.size(); i++){
        for (auto & t : m_rows[i]) {
            std::pair<unsigned, unsigned> p(i, t.var());
            lp_assert(by_rows.find(p) == by_rows.end());
            by_rows[p] = t.get_val();
        }
    }
    std::unordered_map<std::pair<unsigned, unsigned>, T> by_cols;
    for (int i = 0; i < m_columns.size(); i++){
        for (auto & t : m_columns[i]) {
            std::pair<unsigned, unsigned> p(t.var(), i);
            lp_assert(by_cols.find(p) == by_cols.end());
            by_cols[p] = get_val(t);
        }
    }
    lp_assert(by_rows.size() == by_cols.size());

    for (auto & t : by_rows) {
        auto ic = by_cols.find(t.first);
        lp_assert(ic != by_cols.end());
        lp_assert(t.second == ic->second);
    }
}
#endif

template <typename T, typename X>    T static_matrix<T, X>::get_elem(unsigned i, unsigned j) const { // should not be used in efficient code !!!!
    for (auto & t : m_rows[i]) {
        if (t.dead()) continue;
        if (t.var() == j) {
            return t.get_val();
        }
    }
    return numeric_traits<T>::zero();
}


template <typename T, typename X>    T static_matrix<T, X>::get_balance() const {
    T ret = zero_of_type<T>();
    for (unsigned i = 0; i < row_count();  i++) {
        ret += get_row_balance(i);
    }
    return ret;
}

template <typename T, typename X>    T static_matrix<T, X>::get_row_balance(unsigned row) const {
    T ret = zero_of_type<T>();
    for (auto & t : m_rows[row]) {
        if (numeric_traits<T>::is_zero(t.get_val())) continue;
        T a = abs(t.get_val());
        numeric_traits<T>::log(a);
        ret += a * a;
    }
    return ret;
}

template <typename T, typename X> bool static_matrix<T, X>::is_correct() const {
    for (unsigned i = 0; i < m_rows.size(); i++) {
        auto &r = m_rows[i];
        std::unordered_set<unsigned> s;
        for (auto & rc : r) {
            if (rc.dead()) continue;
            if (s.find(rc.var()) != s.end()) {
                return false;
            }
            s.insert(rc.var());
            if (rc.var() >= m_columns.size())
                return false;
            const auto& col = m_columns[rc.var()];
            if (col.cells_size() <= rc.offset())
                return false;
            const auto &cc = col[rc.offset()];
            if (cc.dead())
                return false;
            if (& m_rows[cc.var()][cc.offset()] != & rc) {
                return false;
            }
            if (is_zero(rc.get_val())) {
                return false;
            }
            
        }
    }
    
    for (unsigned j = 0; j < m_columns.size(); j++) {
        auto & c = m_columns[j];
        std::unordered_set<unsigned> s;
        for (auto & cc : c) {
            if (cc.dead())
                continue;
            if (s.find(cc.var()) != s.end()) {
                return false;
            }
            s.insert(cc.var());
            if (cc.var() >= m_rows.size())
                return false;
            auto & rc = m_rows[cc.var()][cc.offset()];
            if (rc.dead())
                return false;
            if (&cc != &m_columns[rc.var()][rc.offset()])
                return false;
        }
    }

    for (auto & row: m_rows) {
        if (! row.is_correct())
            return false;
    }
    for (auto & col: m_columns) {
        if (! col.is_correct())
            return false;
    }
    
    return true;
}

template <typename T, typename X>
void static_matrix<T, X>::remove_element(row_cell<T> & rc) {
    lp_assert(rc.alive());
    unsigned j = rc.var();
    unsigned j_offset = rc.offset();
    auto & col = m_columns[j];
    column_cell & c = col[j_offset];
    unsigned i = c.var();
    unsigned i_offset = c.offset();
    col.delete_at(j_offset);
    m_rows[i].delete_at(i_offset);
}

template <typename T, typename X>
void static_matrix<T, X>::add_new_element(unsigned i, unsigned j, const T& val) {
    auto & row = m_rows[i];
    auto & col = m_columns[j];
    unsigned offset_in_row, offset_in_col;
    row_cell<T>& rc = row.add_cell(j, val, offset_in_row);
    column_cell& cc = col.add_cell(i, offset_in_col);
    rc.offset() = offset_in_col;
    cc.offset() = offset_in_row;
}

}
