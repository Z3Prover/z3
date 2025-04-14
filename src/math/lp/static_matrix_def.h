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
#include <utility>
#include <set>
#include "math/lp/static_matrix.h"
#include "static_matrix.h"
namespace lp {
// each assignment for this matrix should be issued only once!!!

    inline void addmul(double& r, double a, double b) { r += a*b; }
    inline void addmul(mpq& r, mpq const& a, mpq const& b) { r.addmul(a, b); }

    template <typename T, typename X>
    void  static_matrix<T, X>::init_row_columns(unsigned m, unsigned n) {
        SASSERT(m_rows.size() == 0 && m_columns.size() == 0);
        for (unsigned i = 0; i < m; i++) {
            m_rows.push_back(row_strip<T>());
        }
        for (unsigned j = 0; j < n; j++) {
            m_columns.push_back(column_strip());
        }
    }


    template <typename T, typename X> void static_matrix<T, X>:: scan_row_strip_to_work_vector(const row_strip<T> & rvals) {
        for (unsigned j = 0; j < rvals.size(); j++)
            m_work_vector_of_row_offsets[rvals[j].var()] = j;
    }


    template <typename T, typename X> bool static_matrix<T, X>::pivot_row_to_row_given_cell(unsigned i, 
                                                                                            column_cell & c, unsigned pivot_col) {
        unsigned ii = c.var();
        SASSERT(i < row_count() && ii < column_count() && i != ii);
        T alpha = -get_val(c);
        SASSERT(!is_zero(alpha));
        auto & rowii = m_rows[ii];
        remove_element(rowii, rowii[c.offset()]);
        scan_row_strip_to_work_vector(rowii);
        unsigned prev_size_ii = static_cast<unsigned>(rowii.size());
        // run over the pivot row and update row ii
        for (const auto & iv : m_rows[i]) {
            unsigned j = iv.var();
            if (j == pivot_col) continue;
            SASSERT(!is_zero(iv.coeff()));
            int j_offs = m_work_vector_of_row_offsets[j];
            if (j_offs == -1) { // it is a new element
                T alv = alpha * iv.coeff();
                add_new_element(ii, j, alv);
            }
            else {
                addmul(rowii[j_offs].coeff(), iv.coeff(), alpha);
            }
        }
        // clean the work vector
        for (unsigned k = 0; k < prev_size_ii; k++) {
            m_work_vector_of_row_offsets[rowii[k].var()] = -1;
        }

        // remove zeroes
        for (unsigned k = static_cast<unsigned>(rowii.size()); k-- > 0;  ) {
            if (is_zero(rowii[k].coeff()))
                remove_element(rowii, rowii[k]);
        }
        return !rowii.empty();
    }

    
    template <typename T, typename X> void static_matrix<T, X>::add_rows(const mpq& alpha, unsigned i, unsigned k) {
        SASSERT(i < row_count() && k < row_count() && i != k);
        auto & rowk = m_rows[k];
        scan_row_strip_to_work_vector(rowk);
        unsigned prev_size_k = static_cast<unsigned>(rowk.size());
        // run over the pivot row and update row k
        for (const auto & iv : m_rows[i]) {
            unsigned j = iv.var();
            int j_offs = m_work_vector_of_row_offsets[j];
            if (j_offs == -1) { // it is a new element
                T alv = alpha * iv.coeff();
                add_new_element(k, j, alv);
            }
            else {
                addmul(rowk[j_offs].coeff(), iv.coeff(), alpha);
            }
        }
        // clean the work vector
        for (unsigned k = 0; k < prev_size_k; k++) {
            m_work_vector_of_row_offsets[rowk[k].var()] = -1;
        }

        // remove zeroes
        for (unsigned k = static_cast<unsigned>(rowk.size()); k-- > 0;  ) {
            if (is_zero(rowk[k].coeff()))
                remove_element(rowk, rowk[k]);
        }
    }


    template <typename T, typename X>
    inline void static_matrix<T, X>::pivot_row_to_row_given_cell_with_sign(unsigned piv_row_index, 
                                                                           column_cell& c, unsigned pivot_col, int pivot_sign) {
        unsigned ii = c.var();
        SASSERT(ii != piv_row_index);
        T alpha = - get_val(c) * pivot_sign;
        SASSERT(!is_zero(alpha));
        auto & rowii = m_rows[ii];
        remove_element(rowii, rowii[c.offset()]);
        scan_row_strip_to_work_vector(rowii);
        unsigned prev_size_ii = static_cast<unsigned>(rowii.size());
        // run over the pivot row and update row ii
        for (const auto & iv : m_rows[piv_row_index]) {
            unsigned j = iv.var();
            if (j == pivot_col) continue;
            SASSERT(!is_zero(iv.coeff()));
            int j_offs = m_work_vector_of_row_offsets[j];
            if (j_offs == -1) { // it is a new element
                T alv = alpha * iv.coeff();
                add_new_element(ii, j, alv);
            }
            else {
                addmul(rowii[j_offs].coeff(), iv.coeff(), alpha);
            }
        }
        // clean the work vector
        for (unsigned k = 0; k < prev_size_ii; k++) {
            m_work_vector_of_row_offsets[rowii[k].var()] = -1;
        }

        // remove zeroes
        for (unsigned k = static_cast<unsigned>(rowii.size()); k-- > 0;  ) {
            if (is_zero(rowii[k].coeff()))
                remove_element(rowii, rowii[k]);
        }
    }

 
    template<typename T, typename X>
    template<typename TTerm>
    void static_matrix<T, X>::add_term_to_row(const mpq& alpha, TTerm const & term, unsigned ii) {
        auto & rowii = m_rows[ii];
        scan_row_strip_to_work_vector(rowii);
        unsigned prev_size_ii = static_cast<unsigned>(rowii.size());
        // run over the term and update row ii
        for (const auto & iv : term) {
            unsigned j = iv.var();
            SASSERT(!is_zero(iv.coeff()));
            int j_offs = m_work_vector_of_row_offsets[j];
            if (j_offs == -1) { // it is a new element
                add_columns_up_to(j);
                T alv = alpha * iv.coeff();
                add_new_element(ii, j, alv);
            }
            else {
                addmul(rowii[j_offs].coeff(), iv.coeff(), alpha);
            }
        }
        // clean the work vector
        for (unsigned k = 0; k < prev_size_ii; k++) {
            m_work_vector_of_row_offsets[rowii[k].var()] = -1;
        }

        // remove zeroes
        for (unsigned k = static_cast<unsigned>(rowii.size()); k-- > 0;  ) {
            if (is_zero(rowii[k].coeff()))
                remove_element(rowii, rowii[k]);
        }

    }
    template<typename T, typename X>
    template<typename TTerm>
    void static_matrix<T, X>::pivot_term_to_row_given_cell(TTerm const & term, column_cell&c, unsigned pivot_col, int j_sign) {
        unsigned ii = c.var();
        T alpha = - get_val(c) * j_sign;
        SASSERT(!is_zero(alpha));
        auto & rowii = m_rows[ii];
        remove_element(rowii, rowii[c.offset()]);
        scan_row_strip_to_work_vector(rowii);
        unsigned prev_size_ii = static_cast<unsigned>(rowii.size());
        // run over the pivot row and update row ii
        for (const auto & iv : term) {
            unsigned j = iv.var();
            if (j == pivot_col) continue;
            SASSERT(!is_zero(iv.coeff()));
            int j_offs = m_work_vector_of_row_offsets[j];
            if (j_offs == -1) { // it is a new element
                T alv = alpha * iv.coeff();
                add_new_element(ii, j, alv);
            }
            else {
                addmul(rowii[j_offs].coeff(), iv.coeff(), alpha);
            }
        }
        // clean the work vector
        for (unsigned k = 0; k < prev_size_ii; k++) {
            m_work_vector_of_row_offsets[rowii[k].var()] = -1;
        }

        // remove zeroes
        for (unsigned k = static_cast<unsigned>(rowii.size()); k-- > 0;  ) {
            if (is_zero(rowii[k].coeff()))
                remove_element(rowii, rowii[k]);
        }

    }


    template <typename T, typename X> void static_matrix<T, X>::clear() {
        m_work_vector_of_row_offsets.clear();
        m_rows.clear();
        m_columns.clear();
    }

    template <typename T, typename X> void static_matrix<T, X>::init_vector_of_row_offsets() {
        m_work_vector_of_row_offsets.clear();
        m_work_vector_of_row_offsets.resize(column_count(), -1);
    }

    template <typename T, typename X> void static_matrix<T, X>::init_empty_matrix(unsigned m, unsigned n) {
        init_row_columns(m, n);
        init_vector_of_row_offsets();
    }

    template <typename T, typename X> unsigned static_matrix<T, X>::lowest_row_in_column(unsigned col) {
        SASSERT(col < column_count());
        column_strip & colstrip = m_columns[col];
        SASSERT(colstrip.size() > 0);
        unsigned ret = 0;
        for (auto & t : colstrip) {
            if (t.var() > ret) {
                ret = t.var();
            }
        }
        return ret;
    }

    template <typename T, typename X> void static_matrix<T, X>::set(unsigned row, unsigned col, T const & val) {
        if (numeric_traits<T>::is_zero(val)) return;
        SASSERT(row < row_count() && col < column_count());
        auto & r = m_rows[row];
        unsigned offs_in_cols = static_cast<unsigned>(m_columns[col].size());
        m_columns[col].push_back(make_column_cell(row, static_cast<unsigned>(r.size())));
        r.push_back(make_row_cell(col, offs_in_cols, val));
    }

    template <typename T, typename X>
    std::set<std::pair<unsigned, unsigned>>  static_matrix<T, X>::get_domain() {
        std::set<std::pair<unsigned, unsigned>> ret;
        for (unsigned i = 0; i < m_rows.size(); i++) {
            for (auto &cell : m_rows[i]) {
                ret.insert(std::make_pair(i, cell.var()));
            }
        }
        return ret;
    }


    template <typename T, typename X> T static_matrix<T, X>::get_max_abs_in_row(unsigned row) const {
        T ret = numeric_traits<T>::zero();
        for (auto & t : m_rows[row]) {
            T a = abs(t.coeff());
            if (a > ret) {
                ret = a;
            }
        }
        return ret;
    }

    template <typename T, typename X> T static_matrix<T, X>::get_min_abs_in_row(unsigned row) const {
        bool first_time = true;
        T ret = numeric_traits<T>::zero();
        for (auto & t : m_rows[row]) {
            T a = abs(t.coeff());
            if (first_time) {
                ret = a;
                first_time = false;
            } else if (a < ret) {
                ret = a;
            }
        }
        return ret;
    }


    template <typename T, typename X> T static_matrix<T, X>::get_max_abs_in_column(unsigned column) const {
        T ret = numeric_traits<T>::zero();
        for (const auto & t : m_columns[column]) {
            T a = abs(get_val(t));
            if (a > ret) {
                ret = a;
            }
        }
        return ret;
    }

    template <typename T, typename X> T static_matrix<T, X>::get_min_abs_in_column(unsigned column) const {
        bool first_time = true;
        T ret = numeric_traits<T>::zero();
        for (auto & t : m_columns[column]) {
            T a = abs(get_val(t));
            if (first_time) {
                first_time = false;
                ret = a;
            } else if (a < ret) {
                ret = a;
            }
        }
        return ret;
    }

#ifdef Z3DEBUG
    template <typename T, typename X> void static_matrix<T, X>::check_consistency() {
        std::unordered_map<std::pair<unsigned, unsigned>, T> by_rows;
        for (unsigned i = 0; i < m_rows.size(); i++) {
            for (auto & t : m_rows[i]) {
                std::pair<unsigned, unsigned> p(i, t.var());
                SASSERT(by_rows.find(p) == by_rows.end());
                by_rows[p] = t.coeff();
            }
        }
        std::unordered_map<std::pair<unsigned, unsigned>, T> by_cols;
        for (unsigned i = 0; i < m_columns.size(); i++) {
            for (auto & t : m_columns[i]) {
                std::pair<unsigned, unsigned> p(t.var(), i);
                SASSERT(by_cols.find(p) == by_cols.end());
                by_cols[p] = get_val(t);
            }
        }
        SASSERT(by_rows.size() == by_cols.size());

        for (auto & t : by_rows) {
            auto ic = by_cols.find(t.first);
            SASSERT(ic != by_cols.end());
            SASSERT(t.second == ic->second);
        }
    }
#endif


    template <typename T, typename X> void static_matrix<T, X>::cross_out_row(unsigned k) {
#ifdef Z3DEBUG
        check_consistency();
#endif
        cross_out_row_from_columns(k, m_rows[k]);
        fix_row_indices_in_each_column_for_crossed_row(k);
        m_rows.erase(m_rows.begin() + k);
#ifdef Z3DEBUG
        regen_domain();
        check_consistency();
#endif
    }

    template <typename T, typename X> void static_matrix<T, X>::fix_row_indices_in_each_column_for_crossed_row(unsigned k) {
        for (auto & column : m_columns) 
            for (auto& cell : column)
                if (cell.var() > k) 
                    cell.var()--;
    }

    template <typename T, typename X> void static_matrix<T, X>::cross_out_row_from_columns(unsigned k, row_strip<T> & row) {
        for (auto & t : row) {
            cross_out_row_from_column(t.var(), k);
        }
    }

    template <typename T, typename X> void static_matrix<T, X>::cross_out_row_from_column(unsigned col, unsigned k) {
        auto & s = m_columns[col];
        for (unsigned i = 0; i < s.size(); i++) {
            if (s[i].var() == k) {
                s.erase(s.begin() + i);
                break;
            }
        }
    }

    template <typename T, typename X> T static_matrix<T, X>::get_elem(unsigned i, unsigned j) const { // should not be used in efficient code !!!!
        for (auto & t : m_rows[i]) {
            if (t.var() == j) {
                return t.coeff();
            }
        }
        return numeric_traits<T>::zero();
    }

    template <typename T, typename X> T static_matrix<T, X>::get_balance() const {
        T ret = zero_of_type<T>();
        for (unsigned i = 0; i < row_count();  i++) {
            ret += get_row_balance(i);
        }
        return ret;
    }

    template <typename T, typename X> T static_matrix<T, X>::get_row_balance(unsigned row) const {
        T ret = zero_of_type<T>();
        for (auto & t : m_rows[row]) {
            if (numeric_traits<T>::is_zero(t.coeff())) continue;
            T a = abs(t.coeff());
            numeric_traits<T>::log(a);
            ret += a * a;
        }
        return ret;
    }

    template <typename T, typename X> bool static_matrix<T, X>::is_correct() const {
        for (auto & row : m_rows) {
            std::unordered_set<unsigned> s;
            for (auto & rc : row) {
                if (s.find(rc.var()) != s.end()) 
                    return false;
                s.insert(rc.var());
                if (rc.var() >= m_columns.size())
                    return false;
                if (rc.offset() >= m_columns[rc.var()].size())
                    return false;
                if (rc.coeff() != get_val(m_columns[rc.var()][rc.offset()]))
                    return false;
                if (is_zero(rc.coeff())) 
                    return false;            
            }
        }
    
        for (auto & column : m_columns) {
            std::unordered_set<unsigned> s;
            for (auto & cc : column) {
                if (s.find(cc.var()) != s.end()) 
                    return false;
                s.insert(cc.var());
                if (cc.var() >= m_rows.size())
                    return false;
                if (cc.offset() >= m_rows[cc.var()].size())
                    return false;
                if (get_val(cc) != m_rows[cc.var()][cc.offset()].coeff())
                    return false;
            }
        }    
        return true;
    }

    template <typename T, typename X>
    void static_matrix<T, X>::remove_element(std_vector<row_cell<T>> & row_vals, row_cell<T> & row_el_iv) {
        unsigned column_offset = row_el_iv.offset();
        auto & column_vals = m_columns[row_el_iv.var()];
        column_cell& cs = m_columns[row_el_iv.var()][column_offset];
        unsigned row_offset = cs.offset();
        if (column_offset != column_vals.size() - 1) {
            auto & cc = column_vals[column_offset] = column_vals.back(); // copy from the tail
            m_rows[cc.var()][cc.offset()].offset() = column_offset;
        }
    
        if (row_offset != row_vals.size() - 1) {
            auto & rc = row_vals[row_offset] = row_vals.back(); // copy from the tail
            m_columns[rc.var()][rc.offset()].offset() = row_offset;
        }

        column_vals.pop_back();
        row_vals.pop_back();
    }

    template <typename T, typename X>
    void static_matrix<T, X>::add_new_element(unsigned row, unsigned col, const T& val) {
        auto & row_vals = m_rows[row];
        auto & col_vals = m_columns[col];
        unsigned row_el_offs = static_cast<unsigned>(row_vals.size());
        unsigned col_el_offs = static_cast<unsigned>(col_vals.size());
        row_vals.push_back(row_cell<T>(col, col_el_offs, val));
        col_vals.push_back(column_cell(row, row_el_offs));
    }

}
