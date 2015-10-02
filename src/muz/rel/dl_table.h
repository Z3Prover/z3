/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    dl_table.h

Abstract:

    <abstract>

Author:

    Krystof Hoder (t-khoder) 2010-09-01.

Revision History:

--*/
#ifndef DL_TABLE_H_
#define DL_TABLE_H_

#include<iostream>
#include<list>
#include<utility>

#include "ast.h"
#include "bit_vector.h"
#include "buffer.h"
#include "hashtable.h"
#include "map.h"
#include "ref_vector.h"
#include "vector.h"
#include "union_find.h"
#include "dl_base.h"
#include "dl_util.h"
#include "bit_vector.h"


namespace datalog {

    class context;
    class variable_intersection;



    // -----------------------------------
    //
    // hashtable_table
    //
    // -----------------------------------

    class hashtable_table;

    class hashtable_table_plugin : public table_plugin {
        friend class hashtable_table;
    protected:
        class join_fn;
    public:
        typedef hashtable_table table;

        hashtable_table_plugin(relation_manager & manager) 
            : table_plugin(symbol("hashtable"), manager) {}

        virtual table_base * mk_empty(const table_signature & s);

        virtual table_join_fn * mk_join_fn(const table_base & t1, const table_base & t2,
            unsigned col_cnt, const unsigned * cols1, const unsigned * cols2);
    };

    class hashtable_table : public table_base {
        friend class hashtable_table_plugin;
        friend class hashtable_table_plugin::join_fn;

        class our_iterator_core;

        typedef hashtable<table_fact, svector_hash_proc<table_element_hash>, 
            vector_eq_proc<table_fact> > storage;

        storage m_data;

        hashtable_table(hashtable_table_plugin & plugin, const table_signature & sig)
            : table_base(plugin, sig) {}
    public:
        hashtable_table_plugin & get_plugin() const
        { return static_cast<hashtable_table_plugin &>(table_base::get_plugin()); }

        virtual void add_fact(const table_fact & f) {
            m_data.insert(f);
        }
        virtual void remove_fact(const table_element* fact) {
            table_fact f(get_signature().size(), fact);
            m_data.remove(f);
        }
        virtual bool contains_fact(const table_fact & f) const {
            return m_data.contains(f);
        }

        virtual iterator begin() const;
        virtual iterator end() const;

        virtual unsigned get_size_estimate_rows() const { return m_data.size(); }
        virtual unsigned get_size_estimate_bytes() const { return m_data.size()*get_signature().size()*8; }
        virtual bool knows_exact_size() const { return true; }
    };

    // -----------------------------------
    //
    // bitvector_table
    //
    // -----------------------------------

    class bitvector_table;

    class bitvector_table_plugin : public table_plugin {
    public:
        typedef bitvector_table table;

        bitvector_table_plugin(relation_manager & manager) 
            : table_plugin(symbol("bitvector"), manager) {}

        virtual bool can_handle_signature(const table_signature & s);

        virtual table_base * mk_empty(const table_signature & s);
    };

    class bitvector_table : public table_base {
        friend class bitvector_table_plugin;

        class bv_iterator;
        bit_vector m_bv;
        unsigned   m_num_cols;
        unsigned_vector m_shift;
        unsigned_vector m_mask;

        unsigned fact2offset(const table_element* f) const;
        void     offset2fact(unsigned offset, table_fact& f) const;

        bitvector_table(bitvector_table_plugin & plugin, const table_signature & sig);
    public:
        virtual void add_fact(const table_fact & f);
        virtual void remove_fact(const table_element* fact);                   
        virtual bool contains_fact(const table_fact & f) const;
        virtual iterator begin() const;
        virtual iterator end() const;
    };

    // -------------------------------------------
    // Equivalence table.
    // Really: partial equivalence relation table.
    // -------------------------------------------

    class equivalence_table;

    class equivalence_table_plugin : public table_plugin {
        class union_fn;
        class select_equal_and_project_fn;
        class join_project_fn;

        bool is_equivalence_table(table_base const& tbl) const;

    public:
        typedef equivalence_table table;

        equivalence_table_plugin(relation_manager & manager) 
            : table_plugin(symbol("equivalence"), manager) {}

        virtual bool can_handle_signature(const table_signature & s);

        virtual table_base * mk_empty(const table_signature & s);

    protected:
        virtual table_union_fn * mk_union_fn(const table_base & tgt, const table_base & src, 
            const table_base * delta);
        virtual table_transformer_fn * mk_select_equal_and_project_fn(
            const table_base & t, 
            const table_element & value, unsigned col);
        virtual table_join_fn * mk_join_project_fn(const table_base & t1, const table_base & t2,
            unsigned col_cnt, const unsigned * cols1, const unsigned * cols2, unsigned removed_col_cnt, 
            const unsigned * removed_cols);


#if 0
        virtual table_join_fn * mk_join_fn(const table_base & t1, const table_base & t2,
            unsigned col_cnt, const unsigned * cols1, const unsigned * cols2);
        virtual table_transformer_fn * mk_project_fn(const table_base & t, unsigned col_cnt, 
            const unsigned * removed_cols);
        virtual table_transformer_fn * mk_rename_fn(const table_base & t, unsigned permutation_cycle_len,
            const unsigned * permutation_cycle);
            const table_element & value, unsigned col);
        virtual table_intersection_filter_fn * mk_filter_by_negation_fn(const table_base & t, 
                const table_base & negated_obj, unsigned joined_col_cnt, 
                const unsigned * t_cols, const unsigned * negated_cols);
#endif 
    };

    class equivalence_table : public table_base {
        friend class equivalence_table_plugin;

        class eq_iterator;
        union_find_default_ctx m_ctx;
        bit_vector            m_valid;
        union_find<>          m_uf;
        table_base*           m_sparse;

        equivalence_table(equivalence_table_plugin & plugin, const table_signature & sig);
        virtual ~equivalence_table();

        unsigned first(table_fact const& f) const { return static_cast<unsigned>(f[0]); }
        unsigned second(table_fact const& f) const { return static_cast<unsigned>(f[1]); }

        bool is_valid(unsigned entry) const { return entry < m_valid.size() && m_valid.get(entry); }
        bool is_sparse() const { return m_sparse != 0; }

        // iterator over equivalence class of 'n'.
        class class_iterator {
            equivalence_table const& m_parent;
            unsigned           m_current;
            unsigned           m_last;
            bool               m_end;
        public:
            class_iterator(equivalence_table const& s, unsigned n, bool end):
                m_parent(s), m_current(n), m_last(n), m_end(end) {}

            unsigned operator*() { return m_current; }

            class_iterator& operator++() { 
                m_current = m_parent.m_uf.next(m_current); 
                m_end = (m_current == m_last); 
                return *this; 
            }

            bool operator==(const class_iterator & it) const {
                return 
                    (m_end && it.m_end) ||
                    (!m_end && !it.m_end && m_current == it.m_current);
            }
            bool operator!=(const class_iterator & it) const { return !operator==(it); }

        };
        class_iterator class_begin(table_element const& e) const;
        class_iterator class_end(table_element const& e) const;

        void add_fact_sparse(table_fact const& f);
        void mk_sparse();
        

    public:
        virtual void add_fact(const table_fact & f);
        virtual void remove_fact(const table_element* fact);                   
        virtual bool contains_fact(const table_fact & f) const;
        virtual table_base* clone() const;
        virtual iterator begin() const;
        virtual iterator end() const;
        virtual unsigned get_size_estimate_rows() const;
        virtual unsigned get_size_estimate_bytes() const;
        virtual bool knows_exact_size() const;
        virtual void display(std::ostream & out) const;

    };

    
};

#endif /* DL_TABLE_H_ */

