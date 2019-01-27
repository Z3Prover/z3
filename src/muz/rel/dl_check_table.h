/*++
Copyright (c) 2010 Microsoft Corporation

Module Name:

    dl_check_table.h

Abstract:

    <abstract>

Author:

    Nikolaj Bjorner (nbjorner) 2010-11-15
    

Revision History:

--*/

#ifndef DL_CHECK_TABLE_H_
#define DL_CHECK_TABLE_H_

#include "muz/rel/dl_base.h"
#include "ast/dl_decl_plugin.h"
#include "muz/rel/dl_relation_manager.h"

namespace datalog {
    class check_table;

    class check_table_plugin : public table_plugin {
        friend class check_table;
        table_plugin& m_checker;
        table_plugin& m_tocheck;
        unsigned m_count;
    protected:
        class join_fn;
        class join_project_fn;
        class union_fn;
        class transformer_fn;
        class rename_fn;
        class project_fn;
        class select_equal_and_project_fn;
        class filter_equal_fn;
        class filter_identical_fn;
        class filter_interpreted_fn;
        class filter_interpreted_and_project_fn;
        class filter_by_negation_fn;

    public:
        check_table_plugin(relation_manager & manager, symbol const& checker, symbol const& tocheck) 
            : table_plugin(symbol("check"), manager),
            m_checker(*manager.get_table_plugin(checker)),
            m_tocheck(*manager.get_table_plugin(tocheck)), m_count(0) {}

        table_base * mk_empty(const table_signature & s) override;

        table_join_fn * mk_join_fn(const table_base & t1, const table_base & t2,
            unsigned col_cnt, const unsigned * cols1, const unsigned * cols2) override;
        table_join_fn * mk_join_project_fn(const table_base & t1, const table_base & t2,
            unsigned col_cnt, const unsigned * cols1, const unsigned * cols2, unsigned removed_col_cnt,
            const unsigned * removed_cols) override;
        table_union_fn * mk_union_fn(const table_base & tgt, const table_base & src,
            const table_base * delta) override;
        table_transformer_fn * mk_project_fn(const table_base & t, unsigned col_cnt,
            const unsigned * removed_cols) override;
        table_transformer_fn * mk_select_equal_and_project_fn(const table_base & t,
            const table_element & value, unsigned col) override;
        table_transformer_fn * mk_rename_fn(const table_base & t, unsigned permutation_cycle_len,
            const unsigned * permutation_cycle) override;
        table_mutator_fn * mk_filter_identical_fn(const table_base & t, unsigned col_cnt,
            const unsigned * identical_cols) override;
        table_mutator_fn * mk_filter_equal_fn(const table_base & t, const table_element & value,
            unsigned col) override;
        table_mutator_fn * mk_filter_interpreted_fn(const table_base & t, app * condition) override;
        table_transformer_fn * mk_filter_interpreted_and_project_fn(const table_base & t,
            app * condition, unsigned removed_col_cnt, const unsigned * removed_cols) override;
        table_intersection_filter_fn * mk_filter_by_negation_fn(
            const table_base & t,
            const table_base & negated_obj, unsigned joined_col_cnt,
            const unsigned * t_cols, const unsigned * negated_cols) override;

        bool can_handle_signature(table_signature const& s) override;

    private:
        static check_table& get(table_base& r);

        static check_table const & get(table_base const& r);  

        static table_base& checker(table_base& r);
        static table_base const& checker(table_base const& r);
        static table_base* checker(table_base* r);
        static table_base const* checker(table_base const* r);
        static table_base& tocheck(table_base& r);
        static table_base const& tocheck(table_base const& r);
        static table_base* tocheck(table_base* r);
        static table_base const* tocheck(table_base const* r);
    };

    class check_table : public table_base {
        friend class check_table_plugin;

        table_base* m_checker;
        table_base* m_tocheck;
            
        check_table(check_table_plugin & p, const table_signature & sig);
        check_table(check_table_plugin & p, const table_signature & sig, table_base* tocheck, table_base* checker);

        ~check_table() override;

        bool well_formed() const;

    public:

        check_table_plugin & get_plugin() const { 
            return static_cast<check_table_plugin &>(table_base::get_plugin()); 
        }

        bool empty() const override;
        void add_fact(const table_fact & f) override;
        void remove_fact(const table_element*  fact) override;
        bool contains_fact(const table_fact & f) const override;
        table_base * complement(func_decl* p, const table_element * func_columns = nullptr) const override;
        table_base * clone() const override;

        iterator begin() const override { SASSERT(well_formed()); return m_tocheck->begin(); }
        iterator end() const override { return m_tocheck->end(); }

        unsigned get_size_estimate_rows() const override { return m_tocheck->get_size_estimate_rows(); }
        unsigned get_size_estimate_bytes() const override { return m_tocheck->get_size_estimate_bytes(); }
    };

 };

#endif /* DL_CHECK_TABLE_H_ */
