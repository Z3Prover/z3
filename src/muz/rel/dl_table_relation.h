/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    dl_table_relation.h

Abstract:

    <abstract>

Author:

    Krystof Hoder (t-khoder) 2010-09-24.

Revision History:

--*/
#ifndef DL_TABLE_RELATION_H_
#define DL_TABLE_RELATION_H_


#include "dl_base.h"
#include "dl_util.h"

namespace datalog {

    class table_relation;

    class table_relation_plugin : public relation_plugin {
        friend class table_relation;

        class tr_join_project_fn;
        class tr_transformer_fn;
        class universal_target_union_fn;
        class tr_union_fn;
        class tr_mutator_fn;
        class tr_intersection_filter_fn;

        table_plugin & m_table_plugin;

        static symbol create_plugin_name(const table_plugin & p);
    public:
        table_relation_plugin(table_plugin & tp, relation_manager & manager) 
            : relation_plugin(create_plugin_name(tp), manager, ST_TABLE_RELATION), m_table_plugin(tp) {}

        table_plugin & get_table_plugin() { return m_table_plugin; }

        virtual bool can_handle_signature(const relation_signature & s);
        
        virtual relation_base * mk_empty(const relation_signature & s);
        virtual relation_base * mk_full_relation(const relation_signature & s, func_decl* p, family_id kind);
        relation_base * mk_from_table(const relation_signature & s, table_base * t);

    protected:
        virtual relation_join_fn * mk_join_fn(const relation_base & t1, const relation_base & t2,
            unsigned col_cnt, const unsigned * cols1, const unsigned * cols2);
        virtual relation_join_fn * mk_join_project_fn(const relation_base & t1, const relation_base & t2,
            unsigned joined_col_cnt, const unsigned * cols1, const unsigned * cols2, unsigned removed_col_cnt, 
            const unsigned * removed_cols);
        virtual relation_transformer_fn * mk_project_fn(const relation_base & t, unsigned col_cnt, 
            const unsigned * removed_cols);
        virtual relation_transformer_fn * mk_rename_fn(const relation_base & t, unsigned permutation_cycle_len, 
            const unsigned * permutation_cycle);
        virtual relation_transformer_fn * mk_permutation_rename_fn(const relation_base & t, 
            const unsigned * permutation);
        virtual relation_union_fn * mk_union_fn(const relation_base & tgt, const relation_base & src, 
            const relation_base * delta);
        virtual relation_mutator_fn * mk_filter_identical_fn(const relation_base & t, unsigned col_cnt, 
            const unsigned * identical_cols);
        virtual relation_mutator_fn * mk_filter_equal_fn(const relation_base & t, const relation_element & value, 
            unsigned col);
        virtual relation_mutator_fn * mk_filter_interpreted_fn(const relation_base & t, app * condition);
        virtual relation_transformer_fn * mk_filter_interpreted_and_project_fn(const relation_base & t,
            app * condition, unsigned removed_col_cnt, const unsigned * removed_cols);
        virtual relation_intersection_filter_fn * mk_filter_by_intersection_fn(const relation_base & t, 
            const relation_base & src, unsigned joined_col_cnt, const unsigned * t_cols, const unsigned * src_cols);
        virtual relation_intersection_filter_fn * mk_filter_by_negation_fn(const relation_base & t, 
            const relation_base & negated_obj, unsigned joined_col_cnt, 
            const unsigned * t_cols, const unsigned * negated_cols);
        virtual relation_transformer_fn * mk_select_equal_and_project_fn(const relation_base & t, 
            const relation_element & value, unsigned col);
    };

    class table_relation : public relation_base {
        friend class table_relation_plugin;
        friend class table_relation_plugin::tr_join_project_fn;
        friend class table_relation_plugin::tr_transformer_fn;

        scoped_rel<table_base> m_table;

        /**
           \brief Create a \c table_relation object.

           The newly created object takes ownership of the \c table object.
        */
        table_relation(table_relation_plugin & p, const relation_signature & s, table_base * table) 
            : relation_base(p, s), m_table(table) { 
            SASSERT(s.size()==table->get_signature().size()); 
        }
    public:

        table_relation_plugin & get_plugin() const { 
            return static_cast<table_relation_plugin &>(relation_base::get_plugin());
        }

        table_base & get_table() { return *m_table; }
        const table_base & get_table() const { return *m_table; }

        virtual bool empty() const { return m_table->empty(); }

        void add_table_fact(const table_fact & f);

        virtual void add_fact(const relation_fact & f);
        virtual bool contains_fact(const relation_fact & f) const;
        virtual relation_base * clone() const;
        virtual relation_base * complement(func_decl* p) const;
        virtual void to_formula(expr_ref& fml) const { get_table().to_formula(get_signature(), fml); }

        virtual void display(std::ostream & out) const {
            get_table().display(out);
        }
        virtual void display_tuples(func_decl & pred, std::ostream & out) const;

        virtual unsigned get_size_estimate_rows() const { return m_table->get_size_estimate_rows(); }
        virtual unsigned get_size_estimate_bytes() const { return m_table->get_size_estimate_bytes(); }
        virtual bool knows_exact_size() const { return m_table->knows_exact_size(); }
    };

};

#endif /* DL_TABLE_RELATION_H_ */

