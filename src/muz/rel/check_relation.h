/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    check_relation.h

Abstract:

    Checked relation. 
    Each operation on an underlying relation is checked for correctness.

Author:

    Nikolaj Bjorner (nbjorner) 2014-09-23

Revision History:


--*/

#pragma once

#include "muz/rel/doc.h"
#include "muz/rel/dl_base.h"

namespace datalog {
    class check_relation_plugin;
    class check_relation;
    
    class check_relation : public relation_base {
        friend class check_relation_plugin;
        ast_manager&    m;
        relation_base*  m_relation;
        expr_ref        m_fml;
        void check_equiv(char const* objective, expr* f1, expr* f2) const;
        expr_ref mk_eq(relation_fact const& f) const;
    public:
        check_relation(check_relation_plugin& p, relation_signature const& s, relation_base* r);
        ~check_relation() override;
        void reset() override;
        void add_fact(const relation_fact & f) override;
        void add_new_fact(const relation_fact & f) override;
        bool contains_fact(const relation_fact & f) const override;
        check_relation * clone() const override;
        check_relation * complement(func_decl*) const override;
        void to_formula(expr_ref& fml) const override;
        check_relation_plugin& get_plugin() const; 
        bool fast_empty() const override;
        bool empty() const override;
        void display(std::ostream& out) const override;
        bool is_precise() const override { return m_relation->is_precise(); }
        unsigned get_size_estimate_rows() const override { return m_relation->get_size_estimate_rows(); }
        relation_base&  rb() { return *m_relation; }
        relation_base const& rb() const { return *m_relation; }
        expr_ref ground(expr* fml) const;
        void consistent_formula();
    };

    class check_relation_plugin : public relation_plugin {
        friend class check_relation;
        
        class join_fn;
        class join_project_fn;
        class project_fn;
        class union_fn;
        class rename_fn;
        class filter_equal_fn;
        class filter_identical_fn;
        class filter_interpreted_fn;
        class filter_by_negation_fn;        
        class filter_by_union_fn;
        class filter_proj_fn;
        class negation_filter_fn;
        ast_manager& m;
        relation_plugin* m_base;
        static check_relation& get(relation_base& r);
        static check_relation* get(relation_base* r);
        static check_relation const & get(relation_base const& r);   
        expr_ref ground(relation_base const& rb, expr* fml) const;
        expr_ref ground(relation_base const& rb) const;

        expr_ref mk_project(
            relation_signature const& sig, 
            expr* fml, unsigned_vector const& removed_cols);

        expr_ref mk_join(
            relation_base const& t1, relation_base const& t2, 
            unsigned_vector const& cols1, unsigned_vector const& cols2);
    public:
        check_relation_plugin(relation_manager& rm);
        ~check_relation_plugin() override;
        void set_plugin(relation_plugin* p) { m_base = p; }

        bool can_handle_signature(const relation_signature & s) override;
        static symbol get_name() { return symbol("check_relation"); }
        relation_base * mk_empty(const relation_signature & s) override;
        relation_base * mk_full(func_decl* p, const relation_signature & s) override;
        relation_join_fn * mk_join_fn(const relation_base & t1, const relation_base & t2,
            unsigned col_cnt, const unsigned * cols1, const unsigned * cols2) override;
        relation_join_fn * mk_join_project_fn(
            const relation_base & t1, const relation_base & t2,
            unsigned col_cnt, const unsigned * cols1, const unsigned * cols2,
            unsigned removed_col_cnt, const unsigned * removed_cols) override;
        relation_transformer_fn * mk_project_fn(const relation_base & t, unsigned col_cnt,
            const unsigned * removed_cols) override;
        relation_transformer_fn * mk_rename_fn(const relation_base & t, unsigned permutation_cycle_len,
            const unsigned * permutation_cycle) override;
        relation_union_fn * mk_union_fn(const relation_base & tgt, const relation_base & src,
            const relation_base * delta) override;
        relation_union_fn * mk_widen_fn(const relation_base & tgt, const relation_base & src,
            const relation_base * delta) override;
        relation_mutator_fn * mk_filter_identical_fn(const relation_base & t, unsigned col_cnt,
            const unsigned * identical_cols) override;
        relation_mutator_fn * mk_filter_equal_fn(const relation_base & t, const relation_element & value,
            unsigned col) override;
        relation_mutator_fn * mk_filter_interpreted_fn(const relation_base & t, app * condition) override;
        relation_intersection_filter_fn * mk_filter_by_negation_fn(
            const relation_base& t,
            const relation_base& neg, unsigned joined_col_cnt, const unsigned *t_cols,
            const unsigned *negated_cols) override;
        relation_transformer_fn * mk_filter_interpreted_and_project_fn(
            const relation_base & t, app * condition,
            unsigned removed_col_cnt, const unsigned * removed_cols) override;

        void verify_join(relation_base const& t1, relation_base const& t2, relation_base const& t,
                         unsigned_vector const& cols1, unsigned_vector const& cols2);


        void verify_filter(expr* fml0, relation_base const& t, expr* cond);

        void verify_union(expr* fml0, relation_base const& src, relation_base const& dst, 
                          expr* delta0, relation_base const* delta);

        void verify_permutation(
            relation_base const& src, relation_base const& dst, 
            unsigned_vector const& cycle);

        void verify_project(
            relation_base const& src, expr* f1, 
            relation_base const& dst, expr* f2,
            unsigned_vector const& removed_cols);

        void verify_project(
            relation_base const& src, 
            relation_base const& dst, 
            unsigned_vector const& removed_cols);

        void verify_filter_project(
            relation_base const& src, relation_base const& dst, 
            app* cond, unsigned_vector const& removed_cols);

        void verify_join_project(
            relation_base const& t1, relation_base const& t2, relation_base const& t,
            unsigned_vector const& cols1, unsigned_vector const& cols2, unsigned_vector const& rm_cols);

        void check_equiv(char const* objective, expr* f1, expr* f2);

        void check_contains(char const* objective, expr* f1, expr* f2);

        void verify_filter_by_negation(
            expr* dst0, 
            relation_base  const& dst,
            relation_base  const& neg,
            unsigned_vector const& dst_eq,
            unsigned_vector const& neg_eq);
    };
};
       

