/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    sparse_matrix.h

Abstract:

    
Author:

    Nikolaj Bjorner (nbjorner) 2014-01-15

Notes:

--*/

#ifndef _SPARSE_MATRIX_H_
#define _SPARSE_MATRIX_H_

#include "mpq_inf.h"
#include "statistics.h"

namespace simplex {

    template<typename Ext>
    class sparse_matrix {
    public:
        typedef typename Ext::numeral numeral;
        typedef typename Ext::scoped_numeral scoped_numeral;
        typedef typename Ext::manager manager;
        typedef unsigned var_t;

        struct row_entry {
            numeral         m_coeff;
            var_t           m_var;
            row_entry(numeral const& c, var_t v): m_coeff(c), m_var(v) {}
        };

    private:
        
        struct stats {
            unsigned m_add_rows;
            stats() { reset(); }
            void reset() {
                memset(this, 0, sizeof(*this));
            }
        };

        static const int dead_id = -1;

        /**
           \brief A row_entry is:  m_var*m_coeff

           m_col_idx points to the place in the
           column where the variable occurs.
        */
        struct _row_entry : public row_entry {
            union {
                int     m_col_idx;
                int     m_next_free_row_entry_idx;
            };            
            _row_entry(numeral const & c, var_t v): row_entry(c, v), m_col_idx(0) {}
            _row_entry() : row_entry(numeral(), dead_id), m_col_idx(0) {}
            bool is_dead() const { return row_entry::m_var == dead_id; }
        };

        /**
           \brief A column entry points to the row and the row_entry within the row 
           that has a non-zero coefficient on the variable associated
           with the column entry.
        */
        struct col_entry {
            int m_row_id;
            union {
                int m_row_idx;
                int m_next_free_col_entry_idx;
            };
            col_entry(int r, int i): m_row_id(r), m_row_idx(i) {}
            col_entry(): m_row_id(0), m_row_idx(0) {}            
            bool is_dead() const { return m_row_id == dead_id; }
        };
     
        struct column;

        /**
           \brief A row contains a base variable and set of
           row_entries. The base variable must occur in the set of
           row_entries with coefficient 1.
        */
        struct _row {
            vector<_row_entry> m_entries;
            unsigned           m_size;           // the real size, m_entries contains dead row_entries.
            int                m_first_free_idx; // first available position.
            _row();
            unsigned size() const { return m_size; }
            unsigned num_entries() const { return m_entries.size(); }
            void reset(manager& m);
            _row_entry & add_row_entry(unsigned & pos_idx);
            void del_row_entry(unsigned idx);
            void compress(manager& m, vector<column> & cols); 
            void compress_if_needed(manager& _m, vector<column> & cols);
            void save_var_pos(svector<int> & result_map, unsigned_vector& idxs) const;
            //bool is_coeff_of(var_t v, numeral const & expected) const;
            int get_idx_of(var_t v) const;
        };
        
        /**
           \brief A column stores in which rows a variable occurs.
           The column may have free/dead entries. The field m_first_free_idx
           is a reference to the first free/dead entry.
        */
        struct column {
            svector<col_entry> m_entries;
            unsigned           m_size; 
            int                m_first_free_idx;
            mutable unsigned   m_refs;
            
            column():m_size(0), m_first_free_idx(-1), m_refs(0) {}
            unsigned size() const { return m_size; }
            unsigned num_entries() const { return m_entries.size(); }
            void reset();
            void compress(vector<_row> & rows);
            void compress_if_needed(vector<_row> & rows);
            //void compress_singleton(vector<_row> & rows, unsigned singleton_pos);
            col_entry const * get_first_col_entry() const;
            col_entry & add_col_entry(int & pos_idx);
            void del_col_entry(unsigned idx);
        };

        manager&                m;
        vector<_row>            m_rows;
        svector<unsigned>       m_dead_rows;        // rows to recycle
        vector<column>          m_columns;          // per var
        svector<int>            m_var_pos;          // temporary map from variables to positions in row
        unsigned_vector         m_var_pos_idx;      // indices in m_var_pos
        stats                   m_stats;

        bool well_formed_row(unsigned row_id) const;
        bool well_formed_column(unsigned column_id) const;
        void del_row_entry(_row& r, unsigned pos);

    public:

        sparse_matrix(manager& _m): m(_m) {}
        ~sparse_matrix();
        void reset();
        
        class row {
            unsigned m_id;            
        public:
            explicit row(unsigned r):m_id(r) {}
            row():m_id(UINT_MAX) {}
            bool operator!=(row const& other) const {
                return m_id != other.m_id;
            }
            unsigned id() const { return m_id; }
        };

        void ensure_var(var_t v);
        
        row mk_row();
        void add_var(row r, numeral const& n, var_t var);
        void add(row r, numeral const& n, row src);
        void mul(row r, numeral const& n);
        void neg(row r);
        void del(row r);

        void gcd_normalize(row const& r, scoped_numeral& g);

        class row_iterator {
            friend class sparse_matrix;
            unsigned   m_curr;
            _row &     m_row;
            void move_to_used() {
                while (m_curr < m_row.num_entries() && 
                       m_row.m_entries[m_curr].is_dead()) {
                    ++m_curr;
                }
            }
            row_iterator(_row & r, bool begin): 
                m_curr(0), m_row(r) {
                if (begin) {
                    move_to_used();
                }
                else {
                    m_curr = m_row.num_entries();
                }
            }            
        public:
            row_entry & operator*() const { return m_row.m_entries[m_curr]; }
            row_entry * operator->() const { return &(operator*()); }
            row_iterator & operator++() { ++m_curr; move_to_used(); return *this; }
            row_iterator operator++(int) { row_iterator tmp = *this; ++*this; return tmp; }
            bool operator==(row_iterator const & it) const { return m_curr == it.m_curr; }
            bool operator!=(row_iterator const & it) const { return m_curr != it.m_curr; }           
        };

        row_iterator row_begin(row const& r) { return row_iterator(m_rows[r.id()], true); }
        row_iterator row_end(row const& r) { return row_iterator(m_rows[r.id()], false); }

        unsigned column_size(var_t v) const { return m_columns[v].size(); }

        class col_iterator {
            friend class sparse_matrix;
            unsigned             m_curr;
            column const&        m_col;
            vector<_row> const&  m_rows;
            void move_to_used() {
                while (m_curr < m_col.num_entries() && m_col.m_entries[m_curr].is_dead()) {
                    ++m_curr;
                }
            }
            col_iterator(column const& c, vector<_row> const& r, bool begin): 
                m_curr(0), m_col(c), m_rows(r) {
                ++m_col.m_refs;
                if (begin) {
                    move_to_used();
                }
                else {
                    m_curr = m_col.num_entries();
                }
            }
        public:
            ~col_iterator() {
                --m_col.m_refs;
            }

            row get_row() { 
                return row(m_col.m_entries[m_curr].m_row_id); 
            }
            row_entry const& get_row_entry() {
                col_entry const& c = m_col.m_entries[m_curr];
                int row_id = c.m_row_id;
                return m_rows[row_id].m_entries[c.m_row_idx];
            }
            
            col_iterator & operator++() { ++m_curr; move_to_used(); return *this; }
            col_iterator operator++(int) { col_iterator tmp = *this; ++*this; return tmp; }
            bool operator==(col_iterator const & it) const { return m_curr == it.m_curr; }
            bool operator!=(col_iterator const & it) const { return m_curr != it.m_curr; }           
        };

        col_iterator col_begin(int v) const { return col_iterator(m_columns[v], m_rows, true); }
        col_iterator col_end(int v) const { return col_iterator(m_columns[v], m_rows, false); }

        void display(std::ostream& out);
        void display_row(std::ostream& out, row const& r);
        bool well_formed() const;

        void collect_statistics(::statistics & st) const;

    };

    struct mpz_ext {
        typedef mpz                 numeral;
        typedef scoped_mpz          scoped_numeral;
        typedef unsynch_mpz_manager manager;
        typedef mpq_inf             eps_numeral;
        typedef unsynch_mpq_inf_manager eps_manager;
    };
    
    struct mpq_ext {
        typedef mpq                 numeral;
        typedef scoped_mpq          scoped_numeral;
        typedef unsynch_mpq_manager manager;
        typedef mpq_inf             eps_numeral;
        typedef unsynch_mpq_inf_manager eps_manager;
    };

};


#endif
