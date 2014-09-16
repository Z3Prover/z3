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
        friend class udoc_relation;
        doc_manager&    dm;
        udoc            m_elems;
        unsigned_vector m_column_info;
        static unsigned num_signature_bits(bv_util& bv, relation_signature const& sig);
        doc* fact2doc(relation_fact const& f) const;        
    public:
        udoc_relation(udoc_plugin& p, relation_signature const& s);
        virtual ~udoc_relation();
        virtual void reset();
        virtual void add_fact(const relation_fact & f);
        virtual bool contains_fact(const relation_fact & f) const;
        virtual udoc_relation * clone() const;
        virtual udoc_relation * complement(func_decl*) const;
        virtual void to_formula(expr_ref& fml) const;
        udoc_plugin& get_plugin() const; 
        virtual bool empty() const { return m_elems.empty(); }
        virtual void display(std::ostream& out) const;
        virtual bool is_precise() const { return true; }

        doc_manager& get_dm() const { return dm; }
        udoc const& get_udoc() const { return m_elems; }
        udoc& get_udoc() { return m_elems; }
        unsigned get_num_bits() const { return m_column_info.back(); }
        unsigned get_num_cols() const { return m_column_info.size()-1; }
        unsigned column_idx(unsigned col) const { return m_column_info[col]; }
        unsigned column_num_bits(unsigned col) const { return m_column_info[col+1] - m_column_info[col]; }
        void expand_column_vector(unsigned_vector& v, udoc_relation* other = 0) const;
    };

    class udoc_plugin : public relation_plugin {
        friend class udoc_relation;
        class join_fn;
        class project_fn;
        class union_fn;
        class rename_fn;
        class filter_mask_fn;
        class filter_identical_fn;
        class filter_interpreted_fn;
        class filter_by_negation_fn;        
        class filter_by_union_fn;
        ast_manager& m;
        bv_util      bv;
        u_map<doc_manager*> m_dms;
        doc_manager& dm(unsigned sz);
        doc_manager& dm(relation_signature const& sig);
        static udoc_relation& get(relation_base& r);
        static udoc_relation* get(relation_base* r);
        static udoc_relation const & get(relation_base const& r);   

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
        // project join select
    };
};
       
#endif /* _UDOC_RELATION_H_ */

