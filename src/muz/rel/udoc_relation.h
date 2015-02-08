/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    udoc_relation.h

Abstract:

    Relation based on union of DOCs.

Author:

    Nuno Lopes (a-nlopes) 2013-03-01
    Nikolaj Bjorner (nbjorner) 2014-09-15

Revision History:


--*/

#ifndef _UDOC_RELATION_H_
#define _UDOC_RELATION_H_

#include "doc.h"
#include "dl_base.h"

namespace datalog {
    class udoc_plugin;
    class udoc_relation;
    
    class udoc_relation : public relation_base {
        friend class udoc_plugin;
        doc_manager&    dm;
        mutable udoc    m_elems;
        unsigned_vector m_column_info;
        doc* fact2doc(relation_fact const& f) const;        
        expr_ref to_formula(tbv const& t) const;
        expr_ref to_formula(doc const& d) const;
    public:
        udoc_relation(udoc_plugin& p, relation_signature const& s);
        virtual ~udoc_relation();
        virtual void reset();
        virtual void add_fact(const relation_fact & f);
        virtual void add_new_fact(const relation_fact & f);
        virtual bool contains_fact(const relation_fact & f) const;
        virtual udoc_relation * clone() const;
        virtual udoc_relation * complement(func_decl*) const;
        virtual void to_formula(expr_ref& fml) const;
        udoc_plugin& get_plugin() const; 
        virtual bool fast_empty() const { return m_elems.is_empty(); }
        virtual bool empty() const; 
        virtual void display(std::ostream& out) const;
        virtual bool is_precise() const { return true; }
        virtual unsigned get_size_estimate_rows() const { return m_elems.size(); }
        virtual unsigned get_size_estimate_bytes() const;

        doc_manager& get_dm() const { return dm; }
        udoc const& get_udoc() const { return m_elems; }
        udoc& get_udoc() { return m_elems; }
        unsigned get_num_records() const { return m_elems.size(); }
        unsigned get_num_bits() const { return m_column_info.back(); }
        unsigned get_num_cols() const { return m_column_info.size()-1; }
        unsigned column_idx(unsigned col) const { return m_column_info[col]; }
        unsigned column_num_bits(unsigned col) const { return m_column_info[col+1] - m_column_info[col]; }
        void expand_column_vector(unsigned_vector& v, const udoc_relation* other = 0) const;
        void extract_guard(expr* condition, expr_ref& guard, expr_ref& rest) const;
        bool is_guard(expr* g) const;
        bool is_guard(unsigned n, expr* const *g) const;
        void compile_guard(expr* g, udoc& result, bit_vector const& discard_cols) const;
        void extract_equalities(expr* g, expr_ref& rest, subset_ints& equalities, unsigned_vector& roots) const;
        void extract_equalities(
            expr* e1, expr* e2, expr_ref_vector& conds, 
            subset_ints& equalities, unsigned_vector& roots) const;
        void apply_guard(expr* g, udoc& result, bit_vector const& discard_cols) const;
        void apply_guard(expr* g, udoc& result, subset_ints const& equalities, bit_vector const& discard_cols) const;
        bool apply_ground_eq(doc_ref& d, unsigned v, unsigned hi, unsigned lo, expr* c) const;
        bool apply_bv_eq(expr* e1, expr* e2, bit_vector const& discard_cols, udoc& result) const;
        bool is_var_range(expr* e, unsigned& hi, unsigned& lo, unsigned& v) const;
    };

    class udoc_plugin : public relation_plugin {
        friend class udoc_relation;
        class join_fn;
        class join_project_fn;
        class join_project_and_fn;
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
        ast_manager&        m;
        bv_util             bv;
        dl_decl_util        dl;
        u_map<doc_manager*> m_dms;
        bool                m_disable_fast_pass;

        doc_manager& dm(unsigned sz);
        doc_manager& dm(relation_signature const& sig);
        static udoc_relation& get(relation_base& r);
        static udoc_relation* get(relation_base* r);
        static udoc_relation const & get(relation_base const& r);   
        void mk_union(doc_manager& dm, udoc& dst, udoc const& src, udoc* delta);
        bool is_numeral(expr* e, rational& r, unsigned& num_bits);
        unsigned num_sort_bits(expr* e) const { return num_sort_bits(get_ast_manager().get_sort(e)); }
        unsigned num_sort_bits(sort* s) const;
        bool     is_finite_sort(sort* s) const;
        unsigned num_signature_bits(relation_signature const& sig);
        expr* mk_numeral(rational const& r, sort* s);
    public:
        udoc_plugin(relation_manager& rm);
        ~udoc_plugin();
        virtual bool can_handle_signature(const relation_signature & s);
        static symbol get_name() { return symbol("doc"); }
        virtual relation_base * mk_empty(const relation_signature & s);
        virtual relation_base * mk_full(func_decl* p, const relation_signature & s);
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
        virtual relation_intersection_filter_fn * mk_filter_by_negation_fn(
            const relation_base& t,
            const relation_base& neg, unsigned joined_col_cnt, const unsigned *t_cols,
            const unsigned *negated_cols);
        virtual relation_transformer_fn * mk_filter_interpreted_and_project_fn(
            const relation_base & t, app * condition,
            unsigned removed_col_cnt, const unsigned * removed_cols);
        virtual relation_join_fn * mk_join_project_fn(
            relation_base const& t1, relation_base const& t2,
            unsigned joined_col_cnt, const unsigned * cols1, const unsigned * cols2, 
            unsigned removed_col_cnt, const unsigned * removed_cols);
             
        void disable_fast_pass() { m_disable_fast_pass = true; }
    };
};
       
#endif /* _UDOC_RELATION_H_ */

