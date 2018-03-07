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

#include "ast/ast.h"
#include "util/bit_vector.h"
#include "util/buffer.h"
#include "util/hashtable.h"
#include "util/map.h"
#include "util/ref_vector.h"
#include "util/vector.h"
#include "util/union_find.h"
#include "muz/rel/dl_base.h"
#include "muz/base/dl_util.h"
#include "util/bit_vector.h"


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

        table_base * mk_empty(const table_signature & s) override;

        table_join_fn * mk_join_fn(const table_base & t1, const table_base & t2,
            unsigned col_cnt, const unsigned * cols1, const unsigned * cols2) override;
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

        void add_fact(const table_fact & f) override {
            m_data.insert(f);
        }
        void remove_fact(const table_element* fact) override {
            table_fact f(get_signature().size(), fact);
            m_data.remove(f);
        }
        bool contains_fact(const table_fact & f) const override {
            return m_data.contains(f);
        }

        iterator begin() const override;
        iterator end() const override;

        unsigned get_size_estimate_rows() const override { return m_data.size(); }
        unsigned get_size_estimate_bytes() const override { return m_data.size()*get_signature().size()*8; }
        bool knows_exact_size() const override { return true; }
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

        bool can_handle_signature(const table_signature & s) override;

        table_base * mk_empty(const table_signature & s) override;
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
        void add_fact(const table_fact & f) override;
        void remove_fact(const table_element* fact) override;
        bool contains_fact(const table_fact & f) const override;
        iterator begin() const override;
        iterator end() const override;
    };


    
};

#endif /* DL_TABLE_H_ */

