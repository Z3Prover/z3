/*++
Copyright (c) 2010 Microsoft Corporation

Module Name:

    dl_skip_table.h

Abstract:

    <abstract>

Author:

    Nikolaj Bjorner (nbjorner)
    Leonardo de Moura (leonardo) 2010-10-14
    

Revision History:

--*/

#ifndef _DL_SKIP_TABLE_H_
#define _DL_SKIP_TABLE_H_

#include "dl_base.h"
#include "imdd.h"

namespace datalog {
    class skip_table;

    class skip_table_plugin : public table_plugin {
        friend class skip_table;
        imdd_manager m_manager;
    protected:
        class join_fn;
        class join_project_fn;
        class union_fn;
        class transformer_fn;
        class rename_fn;
        class project_fn;
        class filter_equal_fn;
        class filter_not_equal_fn;
        class filter_identical_fn;
        class filter_distinct_fn;
        class filter_by_negation_fn;

        imdd_manager& get_imdd_manager() const { return const_cast<imdd_manager&>(m_manager); }

    public:
        typedef skip_table table;

        skip_table_plugin(relation_manager & manager) 
            : table_plugin(symbol("skip"), manager) {}

        virtual table_base * mk_empty(const table_signature & s);

        virtual table_join_fn * mk_join_fn(const table_base & t1, const table_base & t2,
            unsigned col_cnt, const unsigned * cols1, const unsigned * cols2);
        virtual table_join_fn * mk_join_project_fn(
            const table_base & t1, const table_base & t2,
            unsigned joined_col_cnt, const unsigned * cols1, const unsigned * cols2, 
            unsigned removed_col_cnt, const unsigned * removed_cols);
        virtual table_union_fn * mk_union_fn(const table_base & tgt, const table_base & src, 
            const table_base * delta);
        virtual table_transformer_fn * mk_project_fn(const table_base & t, unsigned col_cnt, 
            const unsigned * removed_cols);
        virtual table_transformer_fn * mk_rename_fn(const table_base & t, unsigned permutation_cycle_len,
            const unsigned * permutation_cycle);
        virtual table_mutator_fn * mk_filter_identical_fn(const table_base & t, unsigned col_cnt, 
            const unsigned * identical_cols);
        virtual table_mutator_fn * mk_filter_equal_fn(const table_base & t, const table_element & value, 
            unsigned col);
        virtual table_mutator_fn * mk_filter_interpreted_fn(const table_base & t, app * condition);
        virtual table_intersection_filter_fn * mk_filter_by_negation_fn(
            const table_base & t, 
            const table_base & negated_obj, unsigned joined_col_cnt, 
            const unsigned * t_cols, const unsigned * negated_cols);

        virtual bool can_handle_signature(table_signature const& s);

    private:
        static skip_table& get(table_base& r);

        static skip_table const & get(table_base const& r);  

        static skip_table* mk_join(table_base const& t1, table_base const& t2, table_signature const& s, 
                        unsigned_vector const& cols_t1, unsigned_vector const& cols_t2);

        static skip_table* mk_join_project(table_base const& t1, table_base const& t2, table_signature const& s, 
                                           unsigned_vector const& cols_t1, unsigned_vector const& cols_t2, unsigned_vector const& proj_cols);

        static skip_table* mk_project(table_base const& src, table_signature const& result_sig, 
                                      unsigned_vector const& cols);

        virtual table_mutator_fn * mk_filter_distinct_fn(const table_base & t, unsigned col1, unsigned col2);

        virtual table_mutator_fn * mk_filter_not_equal_fn(const table_base & t, const table_element & value, 
            unsigned col);

    };

    class skip_table : public table_base {
        friend class skip_table_plugin;
        friend class skip_table_plugin::join_fn;
        friend class skip_table_plugin::union_fn;
        friend class skip_table_plugin::transformer_fn;
        friend class skip_table_plugin::rename_fn;
        friend class skip_table_plugin::project_fn;
        friend class skip_table_plugin::filter_equal_fn;
        friend class skip_table_plugin::filter_not_equal_fn;
        friend class skip_table_plugin::filter_identical_fn;
        friend class skip_table_plugin::filter_distinct_fn;

        class our_iterator_core;

        imdd_ref        m_imdd;  
        unsigned_vector m_fact;

        imdd* get_imdd() const { return m_imdd.get(); }

        imdd_manager& get_imdd_manager() const { return get_plugin().get_imdd_manager(); }

        unsigned const* get_fact(table_element const* f) const;

        bool well_formed() const;

        void update(imdd* n);

        void update(skip_table& t) { update(t.m_imdd); }

        skip_table(skip_table_plugin & p, const table_signature & sig);

        skip_table(skip_table_plugin & p, const table_signature & sig, imdd*);

        skip_table(const skip_table & t);

        virtual ~skip_table();

    public:

        skip_table_plugin & get_plugin() const { 
            return static_cast<skip_table_plugin &>(table_base::get_plugin()); 
        }

        virtual bool empty() const;
        virtual void add_fact(const table_fact & f);
        virtual void remove_fact(const table_element * fact);
        virtual bool contains_fact(const table_fact & f) const;       
        virtual table_base * complement() const;
        virtual table_base * clone() const;

        virtual iterator begin() const;
        virtual iterator end() const;

        virtual unsigned get_size_estimate_rows() const;
        virtual unsigned get_size_estimate_bytes() const;
    };

 };

 #endif /* _DL_SKIP_TABLE_H_ */
