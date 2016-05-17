/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    sparse_matrix_def.h

Abstract:

    
Author:

    Nikolaj Bjorner (nbjorner) 2014-01-15

Notes:

    mainly hoisted from theory_arith.h and theory_arith_aux.h

--*/

#ifndef SPARSE_MATRIX_DEF_H_
#define SPARSE_MATRIX_DEF_H_

#include "sparse_matrix.h"
#include "uint_set.h"

namespace simplex {

    // -----------------------------------
    //
    // Rows
    //
    // -----------------------------------

    template<typename Ext>
    sparse_matrix<Ext>::_row::_row():
        m_size(0),
        m_first_free_idx(-1) {
    }

    template<typename Ext>
    void sparse_matrix<Ext>::_row::reset(manager& m) {
        for (unsigned i = 0; i < m_entries.size(); ++i) {
            m.reset(m_entries[i].m_coeff);
        }
        m_entries.reset();
        m_size           = 0;
        m_first_free_idx = -1;
    }

    /**
       \brief Add a new row_entry. The result is a reference to the new row_entry. 
       The position of the new row_entry in the
       row is stored in pos_idx.
    */
    template<typename Ext>
    typename sparse_matrix<Ext>::_row_entry & 
    sparse_matrix<Ext>::_row::add_row_entry(unsigned & pos_idx) {
        m_size++;
        if (m_first_free_idx == -1) {
            pos_idx = m_entries.size();
            m_entries.push_back(_row_entry());
            return m_entries.back();
        }
        else {
            SASSERT(m_first_free_idx >= 0);
            pos_idx = static_cast<unsigned>(m_first_free_idx);
            _row_entry & result = m_entries[pos_idx];
            SASSERT(result.is_dead());
            m_first_free_idx = result.m_next_free_row_entry_idx;
            return result;
        }
    }

    /**
       \brief Delete row_entry at position idx.
    */
    template<typename Ext>
    void sparse_matrix<Ext>::_row::del_row_entry(unsigned idx) {
        _row_entry & t = m_entries[idx];
        SASSERT(!t.is_dead());
        t.m_next_free_row_entry_idx = (unsigned)m_first_free_idx;
        t.m_var = dead_id;
        m_size--;
        m_first_free_idx = idx;
        SASSERT(t.is_dead());
    }

    /**
       \brief Remove holes (i.e., dead entries) from the row. 
    */
    template<typename Ext>
    void sparse_matrix<Ext>::_row::compress(manager& m, vector<column> & cols) {
        unsigned i  = 0;
        unsigned j  = 0;
        unsigned sz = m_entries.size();
        for (; i < sz; i++) {
            _row_entry & t1 = m_entries[i];
            if (!t1.is_dead()) {
                if (i != j) {
                    _row_entry & t2 = m_entries[j];
                    t2.m_coeff.swap(t1.m_coeff);
                    t2.m_var = t1.m_var;
                    t2.m_col_idx = t1.m_col_idx;
                    SASSERT(!t2.is_dead());
                    column & col = cols[t2.m_var];
                    col.m_entries[t2.m_col_idx].m_row_idx = j;
                }
                j++;
            }
        }
        SASSERT(j == m_size);
        // 
        // alternative: update the free-list to point to the
        // tail and avoid shrinking.
        // if m.does not allocate memory (for wrapper around 
        // double), also bypass this step.
        //
        for (unsigned i = m_size; i < m_entries.size(); ++i) {
            m.reset(m_entries[i].m_coeff);
        }
        m_entries.shrink(m_size);
        m_first_free_idx = -1;
    }

    template<typename Ext>
    void sparse_matrix<Ext>::_row::compress_if_needed(manager& m, vector<column> & cols) {
        if (size() *2 < num_entries()) {
            compress(m, cols);
        }
    }

    /**
       \brief Fill the map var -> pos/idx
    */
    template<typename Ext>
    inline void sparse_matrix<Ext>::_row::save_var_pos(svector<int> & result_map, unsigned_vector& idxs) const {
        typename vector<_row_entry>::const_iterator it  = m_entries.begin();
        typename vector<_row_entry>::const_iterator end = m_entries.end();
        unsigned idx = 0;
        for (; it != end; ++it, ++idx) {
            if (!it->is_dead()) {
                result_map[it->m_var] = idx;
                idxs.push_back(it->m_var);
            }
        }
    }


    template<typename Ext>
    int sparse_matrix<Ext>::_row::get_idx_of(var_t v) const {
        typename vector<_row_entry>::const_iterator it  = m_entries.begin();
        typename vector<_row_entry>::const_iterator end = m_entries.end();
        for (unsigned idx = 0; it != end; ++it, ++idx) {
            if (!it->is_dead() && it->m_var == v)
                return idx;
        }
        return -1;
    }

    // -----------------------------------
    //
    // Columns
    //
    // -----------------------------------
    
    template<typename Ext>
    void sparse_matrix<Ext>::column::reset() {
        m_entries.reset();
        m_size           = 0;
        m_first_free_idx = -1;
    }
    
    /**
       \brief Remove holes (i.e., dead entries) from the column.
    */
    template<typename Ext>
    void sparse_matrix<Ext>::column::compress(vector<_row> & rows) {
        unsigned i  = 0;
        unsigned j  = 0;
        unsigned sz = m_entries.size();
        for (; i < sz; i++) {
            col_entry & e1 = m_entries[i];
            if (!e1.is_dead()) {
                if (i != j) {
                    m_entries[j] = e1;
                    _row & r = rows[e1.m_row_id];
                    r.m_entries[e1.m_row_idx].m_col_idx = j;
                }
                j++;
            }
        }
        SASSERT(j == m_size);
        m_entries.shrink(m_size);
        m_first_free_idx = -1;
    }
    
    /**
       \brief Invoke compress if the column contains too many holes (i.e., dead entries).
    */
    template<typename Ext>
    inline void sparse_matrix<Ext>::column::compress_if_needed(vector<_row> & rows) {
        if (size() * 2 < num_entries() && m_refs == 0) {
            compress(rows);
        }
    }

#if 0
    /**
       \brief Special version of compress, that is used when the column contain
       only one entry located at position singleton_pos.
    */
    template<typename Ext>
    void sparse_matrix<Ext>::column::compress_singleton(vector<_row> & rows, unsigned singleton_pos) {
        SASSERT(m_size == 1);
        if (singleton_pos != 0) {
            col_entry & s  = m_entries[singleton_pos];
            m_entries[0]   = s;
            row & r        = rows[s.m_row_id];
            r[s.m_row_idx].m_col_idx = 0;
        }
        m_first_free_idx = -1;
        m_entries.shrink(1);
    }
#endif
    template<typename Ext>
    const typename sparse_matrix<Ext>::col_entry * 
    sparse_matrix<Ext>::column::get_first_col_entry() const {
        typename svector<col_entry>::const_iterator it  = m_entries.begin();
        typename svector<col_entry>::const_iterator end = m_entries.end();
        for (; it != end; ++it) {
            if (!it->is_dead()) {
                return it;
            }
        }
        return 0;
    }

    template<typename Ext>
    typename sparse_matrix<Ext>::col_entry & 
    sparse_matrix<Ext>::column::add_col_entry(int & pos_idx) {
        m_size++;
        if (m_first_free_idx == -1) {
            pos_idx = m_entries.size();
            m_entries.push_back(col_entry());
            return m_entries.back();
        }
        else {
            pos_idx            = m_first_free_idx;
            col_entry & result = m_entries[pos_idx];
            SASSERT(result.is_dead());
            m_first_free_idx = result.m_next_free_col_entry_idx;
            return result;
        }
    }
    
    template<typename Ext>
    void sparse_matrix<Ext>::column::del_col_entry(unsigned idx) {
        col_entry & c = m_entries[idx];
        SASSERT(!c.is_dead());
        c.m_row_id                  = dead_id;
        c.m_next_free_col_entry_idx = m_first_free_idx;
        m_first_free_idx            = idx;
        m_size--;
    }

    // -----------------------------------
    //
    // Matrix
    //
    // -----------------------------------

    template<typename Ext>
    sparse_matrix<Ext>::~sparse_matrix() {
        for (unsigned i = 0; i < m_rows.size(); ++i) {
            _row& r = m_rows[i];
            for (unsigned j = 0; j < r.m_entries.size(); ++j) {
                m.reset(r.m_entries[j].m_coeff);
            }
        }
    }

    template<typename Ext>
    void sparse_matrix<Ext>::reset() {
        m_rows.reset();
        m_dead_rows.reset();
        m_columns.reset();
        m_var_pos.reset();
        m_var_pos_idx.reset();

    }

    template<typename Ext>
    void sparse_matrix<Ext>::ensure_var(var_t v) {
        while (m_columns.size() <= v) {
            m_columns.push_back(column());
            m_var_pos.push_back(-1);
        }
    }

    template<typename Ext>
    typename sparse_matrix<Ext>::row 
    sparse_matrix<Ext>::mk_row() {
        if (m_dead_rows.empty()) {
            row r(m_rows.size());
            m_rows.push_back(_row());            
            return r;
        }
        else {
            row r(m_dead_rows.back());
            m_dead_rows.pop_back();
            return r;
        }
    }

    template<typename Ext>
    void sparse_matrix<Ext>::add_var(row dst, numeral const& n, var_t v) {
        _row& r   = m_rows[dst.id()];
        column& c = m_columns[v];
        unsigned r_idx;
        int c_idx;
        _row_entry & r_entry = r.add_row_entry(r_idx);
        col_entry&   c_entry = c.add_col_entry(c_idx);
        r_entry.m_var     = v;
        m.set(r_entry.m_coeff, n);
        r_entry.m_col_idx = c_idx;
        c_entry.m_row_id  = dst.id();
        c_entry.m_row_idx = r_idx;        
    }

    /**
       \brief Set row1 <- row1 + row2 * n
    */
    template<typename Ext>
    void sparse_matrix<Ext>::add(row row1, numeral const& n, row row2) {
        m_stats.m_add_rows++;
        _row & r1 = m_rows[row1.id()];
        
        r1.save_var_pos(m_var_pos, m_var_pos_idx);

        // 
        // loop over variables in row2,
        // add terms in row2 to row1.
        //

#define ADD_ROW(_SET_COEFF_, _ADD_COEFF_)                               \
        row_iterator it  = row_begin(row2);                             \
        row_iterator end = row_end(row2);                               \
        for (; it != end; ++it) {                                       \
            var_t v = it->m_var;                                        \
            int pos = m_var_pos[v];                                     \
            if (pos == -1) {                                            \
                /* variable v is not in row1 */                         \
                unsigned row_idx;                                       \
                _row_entry & r_entry = r1.add_row_entry(row_idx);       \
                r_entry.m_var         = v;                              \
                m.set(r_entry.m_coeff, it->m_coeff);                    \
                _SET_COEFF_;                                            \
                column & c            = m_columns[v];                   \
                int col_idx;                                            \
                col_entry & c_entry   = c.add_col_entry(col_idx);       \
                r_entry.m_col_idx     = col_idx;                        \
                c_entry.m_row_id      = row1.id();                      \
                c_entry.m_row_idx     = row_idx;                        \
            }                                                           \
            else {                                                      \
                /* variable v is in row1 */                             \
                _row_entry & r_entry   = r1.m_entries[pos];             \
                SASSERT(r_entry.m_var == v);                            \
                _ADD_COEFF_;                                            \
                if (m.is_zero(r_entry.m_coeff)) {                       \
                    del_row_entry(r1, pos);                             \
                }                                                       \
            }                                                           \
        }                                                               \
        ((void) 0)

        if (m.is_one(n)) {
            ADD_ROW({},
                    m.add(r_entry.m_coeff, it->m_coeff, r_entry.m_coeff));
        }
        else if (m.is_minus_one(n)) {
            ADD_ROW(m.neg(r_entry.m_coeff),
                    m.sub(r_entry.m_coeff, it->m_coeff, r_entry.m_coeff));
        }
        else {
            scoped_numeral tmp(m);
            ADD_ROW(m.mul(r_entry.m_coeff, n, r_entry.m_coeff), 
                    m.mul(it->m_coeff, n, tmp);
                    m.add(r_entry.m_coeff, tmp, r_entry.m_coeff));
        }
        
        // reset m_var_pos:
        for (unsigned i = 0; i < m_var_pos_idx.size(); ++i) {
            m_var_pos[m_var_pos_idx[i]] = -1;
        }
        m_var_pos_idx.reset();
        r1.compress_if_needed(m, m_columns);
    }
    

    template<typename Ext>
    void sparse_matrix<Ext>::del_row_entry(_row& r, unsigned pos) {
        _row_entry & r_entry   = r.m_entries[pos];     
        var_t v = r_entry.m_var;
        int col_idx = r_entry.m_col_idx;                                
        r.del_row_entry(pos);                              
        column & c  = m_columns[v];                   
        c.del_col_entry(col_idx);                           
        c.compress_if_needed(m_rows);                       
    }

    /**
       \brief Set row <- -row
    */    
    template<typename Ext>
    void sparse_matrix<Ext>::neg(row r) {
        row_iterator it  = row_begin(r);                             
        row_iterator end = row_end(r);                               
        for (; it != end; ++it) {   
            m.neg(it->m_coeff);
        }                                            
    }

    /**
       \brief Set row <- n*row
    */    
    template<typename Ext>
    void sparse_matrix<Ext>::mul(row r, numeral const& n) {
        SASSERT(!m.is_zero(n));
        if (m.is_one(n)) {
            // no op
        }
        else if (m.is_minus_one(n)) {
            neg(r);
        }
        else {
            row_iterator it  = row_begin(r);                             
            row_iterator end = row_end(r);                               
            for (; it != end; ++it) {   
                m.mul(it->m_coeff, n, it->m_coeff);
            }                     
        }                       
    }

    /**
       \brief Delete row.
    */    
    template<typename Ext>
    void sparse_matrix<Ext>::del(row r) {
        _row& rw = m_rows[r.id()];
        for (unsigned i = 0; i < rw.m_entries.size(); ++i) {
            _row_entry& e = rw.m_entries[i];
            if (!e.is_dead()) {
                del_row_entry(rw, i);
            }
        }
        SASSERT(rw.m_size == 0);
        m_dead_rows.push_back(r.id());
    }

    /**
       \brief normalize coefficients by dividing with they coefficients.
       return the gcd.
    */
    template<typename Ext>
    void sparse_matrix<Ext>::gcd_normalize(row const& r, scoped_numeral& g) {
        g.reset();
        row_iterator it = row_begin(r), end = row_end(r); 
        for (; it != end && !m.is_one(g); ++it) {
            if (m.is_zero(g)) g = it->m_coeff;
            else m.gcd(g, it->m_coeff, g);
        }   
        if (m.is_zero(g)) {
            g = numeral(1);
        }
        if (!m.is_one(g)) {
            row_iterator it2 = row_begin(r);
            for (; it2 != end; ++it2) {
                m.div(it2->m_coeff, g, it2->m_coeff);
            }   
        }
    }

    /**
       \brief well_formed check
    */    
    template<typename Ext>
    bool sparse_matrix<Ext>::well_formed() const {
        for (unsigned i = 0; i < m_rows.size(); ++i) {
            well_formed_row(i);
        }
        for (unsigned i = 0; i < m_columns.size(); ++i) {
            well_formed_column(i);
        }
        return true;
    }

    /**
       \brief well_formed row check
    */    
    template<typename Ext>
    bool sparse_matrix<Ext>::well_formed_row(unsigned row_id) const {
        uint_set vars, dead;
        _row const& r = m_rows[row_id];
        for (unsigned i = 0; i < r.num_entries(); ++i) {
            _row_entry const& e = r.m_entries[i];
            if (e.is_dead()) {
                dead.insert(i);
                continue;
            }
            DEBUG_CODE(
                SASSERT(!vars.contains(e.m_var));
                SASSERT(!m.is_zero(e.m_coeff));            
                SASSERT(e.m_var != dead_id);
                col_entry const& c = m_columns[e.m_var].m_entries[e.m_col_idx];
                SASSERT((unsigned)c.m_row_id == row_id);
                SASSERT((unsigned)c.m_row_idx == i););
            vars.insert(e.m_var);
        }                  
        int idx = r.m_first_free_idx;
        while (idx != -1) {
            SASSERT(dead.contains(idx));
            dead.remove(idx);
            idx = r.m_entries[idx].m_next_free_row_entry_idx;
        }
        SASSERT(dead.empty());
        return true;
    }

    /**
       \brief well_formed column check
    */    
    template<typename Ext>
    bool sparse_matrix<Ext>::well_formed_column(var_t v) const {
        uint_set rows, dead;
        column const& col = m_columns[v];
        for (unsigned i = 0; i < col.num_entries(); ++i) {
            col_entry const& c = col.m_entries[i];
            if (c.is_dead()) {
                dead.insert(i);
                continue;
            }
            SASSERT(!rows.contains(c.m_row_id));
            DEBUG_CODE(
                _row const& row = m_rows[c.m_row_id];
                _row_entry const& r = row.m_entries[c.m_row_idx];
                SASSERT(r.m_var == v); 
                SASSERT((unsigned)r.m_col_idx == i););
            rows.insert(c.m_row_id);
        }                           
        int idx = col.m_first_free_idx;
        while (idx != -1) {
            SASSERT(dead.contains(idx));
            dead.remove(idx);
            idx = col.m_entries[idx].m_next_free_col_entry_idx;
        }
        SASSERT(dead.empty());
        return true;
    }

    /**
       \brief statistics
    */    
    template<typename Ext>
    void sparse_matrix<Ext>::collect_statistics(::statistics & st) const {
        st.update("simplex add rows", m_stats.m_add_rows);
    }


    /**
       \brief display method
    */    
    template<typename Ext>
    void sparse_matrix<Ext>::display(std::ostream& out) {
        for (unsigned i = 0; i < m_rows.size(); ++i) {
            if (m_rows[i].size() == 0) continue;
            display_row(out, row(i));
        }
    }

    template<typename Ext>
    void sparse_matrix<Ext>::display_row(std::ostream& out, row const& r) {
        row_iterator it = row_begin(r), end = row_end(r); 
        for (; it != end; ++it) {
            m.display(out, it->m_coeff);
            out << "*v" << it->m_var << " ";
        }
        out << "\n";
    }

    

};

#endif
