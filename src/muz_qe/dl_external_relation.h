/*++
Copyright (c) 2010 Microsoft Corporation

Module Name:

    dl_external_relation.h

Abstract:

    <abstract>

Author:

    Nikolaj Bjorner (nbjorner) 2010-05-10

Revision History:

--*/
#ifndef _DL_EXTERNAL_RELATION_H_
#define _DL_EXTERNAL_RELATION_H_

#include "dl_base.h"

namespace datalog {

    class external_relation;

    class external_relation_context {
    public:
        virtual ~external_relation_context() {}

        virtual family_id get_family_id() const = 0;

        // reduce arguments.
        virtual void reduce(func_decl* f, unsigned num_args, expr * const* args, expr_ref& result) = 0;  
        
        // overwrite terms passed in outs vector with values computed by function.
        virtual void reduce_assign(func_decl* f, unsigned num_args, expr * const* args, unsigned num_out, expr* const* outs) = 0;
    };

    class external_relation_plugin : public relation_plugin {

        friend class external_relation;
        class join_fn;
        class project_fn;
        class rename_fn;
        class union_fn;
        class filter_identical_fn;
        class filter_interpreted_fn;
        class negation_filter_fn;

        external_relation_context& m_ext;

    public:
        external_relation_plugin(external_relation_context& ctx, relation_manager & m);

        virtual bool can_handle_signature(const relation_signature & s) { return true; }

        static symbol get_name() { return symbol("external_relation"); }

        virtual relation_base * mk_empty(const relation_signature & s);

        virtual relation_join_fn * mk_join_fn(const relation_base & t1, const relation_base & t2,
            unsigned col_cnt, const unsigned * cols1, const unsigned * cols2);
        virtual relation_transformer_fn * mk_project_fn(const relation_base & t, unsigned col_cnt, 
            const unsigned * removed_cols);
        virtual relation_transformer_fn * mk_rename_fn(const relation_base & t, unsigned permutation_cycle_len, 
            const unsigned * permutation_cycle);
        virtual relation_union_fn * mk_union_fn(const relation_base & tgt, const relation_base & src, 
            const relation_base * delta);
        virtual relation_union_fn * mk_widen_fn(const relation_base & tgt, const relation_base & src, 
            const relation_base * delta);
        virtual relation_mutator_fn * mk_filter_identical_fn(const relation_base & t, unsigned col_cnt, 
            const unsigned * identical_cols);
        virtual relation_mutator_fn * mk_filter_equal_fn(const relation_base & t, const relation_element & value, 
            unsigned col);
        virtual relation_mutator_fn * mk_filter_interpreted_fn(const relation_base & t, app * condition);
        virtual relation_intersection_filter_fn * mk_filter_by_negation_fn(const relation_base & t, 
            const relation_base & negated_obj, unsigned joined_col_cnt, 
            const unsigned * t_cols, const unsigned * negated_cols);

    private:

        static external_relation& get(relation_base& r);
        static external_relation const & get(relation_base const& r);

        void reduce(func_decl* f, unsigned num_args, expr * const* args, expr_ref& result) {
            m_ext.reduce(f, num_args, args, result);
        }

        void reduce_assign(func_decl* f, unsigned num_args, expr * const* args, unsigned num_out, expr* const* outs) {
            m_ext.reduce_assign(f, num_args, args, num_out, outs);
        }

        sort* get_relation_sort(relation_signature const& sig);

        sort* get_column_sort(unsigned col, sort* relation_sort);

        void mk_filter_fn(sort* s, app* condition, func_decl_ref& f);

        family_id get_family_id();
    };

    class external_relation : public relation_base {
        friend class external_relation_plugin;
        friend class external_relation_plugin::join_fn;
        friend class external_relation_plugin::project_fn;
        friend class external_relation_plugin::rename_fn;
        friend class external_relation_plugin::union_fn;
        friend class external_relation_plugin::filter_identical_fn;
        friend class external_relation_plugin::filter_interpreted_fn;
        friend class external_relation_plugin::negation_filter_fn;

        expr_ref                  m_rel;
        func_decl_ref             m_select_fn;
        func_decl_ref             m_store_fn;
        func_decl_ref             m_is_empty_fn;

        unsigned size() const { return get_signature().size(); } 

        sort*    get_sort() const { return m_rel.get_manager().get_sort(m_rel); }

        void mk_accessor(decl_kind k, func_decl_ref& fn, const relation_fact& f, bool destructive, expr_ref& res) const;

        external_relation(external_relation_plugin & p, const relation_signature & s, expr* r);
        virtual ~external_relation();

    public:
        external_relation_plugin & get_plugin() const;

        virtual bool empty() const;

        virtual void add_fact(const relation_fact & f);

        virtual bool contains_fact(const relation_fact & f) const;

        virtual external_relation * clone() const;

        virtual external_relation * complement(func_decl*) const;

        virtual void display(std::ostream & out) const;

        virtual void display_tuples(func_decl & pred, std::ostream & out) const;

        expr*  get_relation() const { return m_rel.get(); }

        virtual void to_formula(expr_ref& fml) const { fml = get_relation(); }
    
    };


};

#endif
