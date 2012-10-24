/*++
Copyright (c) 2010 Microsoft Corporation

Module Name:

    dl_smt_relation.h

Abstract:

    Relation signature represented by signatures that have quantifier elimination.

Author:

    Nikolaj Bjorner (nbjorner) 2010-10-10

Revision History:

--*/
#ifndef _DL_SMT_RELATION_H_
#define _DL_SMT_RELATION_H_

#include "dl_base.h"
#include "front_end_params.h"
#include "params.h"

namespace datalog {

    class smt_relation;

    class smt_relation_plugin : public relation_plugin {

        unsigned     m_counter;

        friend class smt_relation;
        class join_fn;
        class project_fn;
        class rename_fn;
        class union_fn;
        class filter_identical_fn;
        class filter_interpreted_fn;
        class negation_filter_fn;

    public:
        smt_relation_plugin(relation_manager & m);

        virtual bool can_handle_signature(const relation_signature & s);

        static symbol get_name() { return symbol("smt_relation"); }

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

        symbol fresh_name(); 

        front_end_params& get_fparams(); 

        params_ref const& get_params();

        bool is_finite_domain(sort* s) const;

    private:
        static smt_relation& get(relation_base& r);

        static smt_relation const & get(relation_base const& r);        
    };

    class smt_relation : public relation_base {
        friend class smt_relation_plugin;
        friend class smt_relation_plugin::join_fn;
        friend class smt_relation_plugin::project_fn;
        friend class smt_relation_plugin::rename_fn;
        friend class smt_relation_plugin::union_fn;
        friend class smt_relation_plugin::filter_identical_fn;
        friend class smt_relation_plugin::filter_interpreted_fn;
        friend class smt_relation_plugin::negation_filter_fn;

        expr_ref        m_rel;            // relation.
        expr_ref_vector m_bound_vars;
        
        unsigned size() const { return get_signature().size(); } 

        ast_manager& get_manager() const { return get_plugin().get_ast_manager(); }

        smt_relation(smt_relation_plugin & p, const relation_signature & s, expr* r);

        virtual ~smt_relation();

        void instantiate(expr* e, expr_ref& result) const;

        void mk_abstract(expr* e, expr_ref& result) const;

        bool contains(expr* facts);

        bool is_finite_domain() const;

        bool is_well_formed() const;

        void display_finite(std::ostream & out) const;

        void simplify(expr_ref& e) const;

    public:

        virtual bool empty() const;

        virtual void add_fact(const relation_fact & f);

        virtual bool contains_fact(const relation_fact & f) const;
        virtual smt_relation * clone() const;
        virtual smt_relation * complement(func_decl*) const;
        virtual void display(std::ostream & out) const;
        virtual void to_formula(expr_ref& fml) const { fml = get_relation(); simplify(fml); }

        expr* get_relation() const;
        void set_relation(expr* r);
        void add_relation(expr* s); // add s to relation.
        void filter_relation(expr* s); // restrict relation with s
        smt_relation_plugin& get_plugin() const; 

    };
};

#endif
