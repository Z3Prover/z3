/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    dl_sieve_relation.h

Abstract:

    <abstract>

Author:

    Krystof Hoder (t-khoder) 2010-11-11.

Revision History:

--*/

#ifndef _DL_SIEVE_RELATION_H_
#define _DL_SIEVE_RELATION_H_

#include "dl_context.h"
#include "dl_relation_manager.h"

namespace datalog {

    class sieve_relation;

    class sieve_relation_plugin : public relation_plugin {
        friend class sieve_relation;
    public:
        struct rel_spec {
            svector<bool> m_inner_cols;
            family_id m_inner_kind;

            /**
               Create uninitialized rel_spec.
            */
            rel_spec() {} 
            /**
               \c inner_kind==null_family_id means we will not specify a relation kind when requesting
               the relation object from the relation_manager.

               \c inner_kind==null_family_id cannot hold in a specification of existing relation object.
            */
            rel_spec(unsigned sig_sz, const bool * inner_cols, family_id inner_kind=null_family_id)
                : m_inner_cols(sig_sz, inner_cols), m_inner_kind(inner_kind) {}

            bool operator==(const rel_spec & o) const {
                return m_inner_kind==o.m_inner_kind && vectors_equal(m_inner_cols, o.m_inner_cols);
            }

            struct hash {
                unsigned operator()(const rel_spec & s) const {
                    return svector_hash<bool_hash>()(s.m_inner_cols)^s.m_inner_kind;
                }
            };
        };
    private:

        class join_fn;
        class transformer_fn;
        class union_fn;
        class filter_fn;
        class negation_filter_fn;

        rel_spec_store<rel_spec, rel_spec::hash, default_eq<rel_spec> > m_spec_store;

        family_id get_relation_kind(sieve_relation & r, const bool * inner_columns);

        void extract_inner_columns(const relation_signature & s, relation_plugin & inner, 
            svector<bool> & inner_columns);
        void extract_inner_signature(const relation_signature & s, relation_signature & inner_sig);
        void collect_inner_signature(const relation_signature & s, const svector<bool> & inner_columns, 
            relation_signature & inner_sig);
    public:
        static symbol get_name() { return symbol("sieve_relation"); }
        static sieve_relation_plugin& get_plugin(relation_manager & rmgr);

        static sieve_relation& get(relation_base& r);
        static sieve_relation const & get(relation_base const& r);   
        static sieve_relation* get(relation_base* r);
        static sieve_relation const* get(relation_base const* r);

        sieve_relation_plugin(relation_manager & manager);

        virtual void initialize(family_id fid);

        family_id get_relation_kind(const relation_signature & sig, const bool * inner_columns, 
            family_id inner_kind);
        family_id get_relation_kind(const relation_signature & sig, const svector<bool> & inner_columns, 
                family_id inner_kind) {
            SASSERT(sig.size()==inner_columns.size());
            return get_relation_kind(sig, inner_columns.c_ptr(), inner_kind);
        }

        virtual bool can_handle_signature(const relation_signature & s);
        
        virtual relation_base * mk_empty(const relation_signature & s);
        sieve_relation * mk_empty(const sieve_relation & original);
        virtual relation_base * mk_empty(const relation_base & original);
        virtual relation_base * mk_empty(const relation_signature & s, family_id kind);
        sieve_relation * mk_empty(const relation_signature & s, relation_plugin & inner_plugin);

        virtual relation_base * mk_full(func_decl* p, const relation_signature & s);
        sieve_relation * mk_full(func_decl* p, const relation_signature & s, relation_plugin & inner_plugin);


        sieve_relation * mk_from_inner(const relation_signature & s, const bool * inner_columns, 
            relation_base * inner_rel);
        sieve_relation * mk_from_inner(const relation_signature & s, const svector<bool> inner_columns, 
                relation_base * inner_rel) {
            SASSERT(inner_columns.size()==s.size());
            return mk_from_inner(s, inner_columns.c_ptr(), inner_rel);
        }

    protected:

        virtual relation_join_fn * mk_join_fn(const relation_base & t1, const relation_base & t2,
            unsigned col_cnt, const unsigned * cols1, const unsigned * cols2);
        virtual relation_transformer_fn * mk_project_fn(const relation_base & t, unsigned col_cnt, 
            const unsigned * removed_cols);
        virtual relation_transformer_fn * mk_rename_fn(const relation_base & t, unsigned permutation_cycle_len, 
            const unsigned * permutation_cycle);
        virtual relation_union_fn * mk_union_fn(const relation_base & tgt, const relation_base & src, 
            const relation_base * delta);
        virtual relation_mutator_fn * mk_filter_identical_fn(const relation_base & t, unsigned col_cnt, 
            const unsigned * identical_cols);
        virtual relation_mutator_fn * mk_filter_equal_fn(const relation_base & t, const relation_element & value, 
            unsigned col);
        virtual relation_mutator_fn * mk_filter_interpreted_fn(const relation_base & t, app * condition);
        virtual relation_intersection_filter_fn * mk_filter_by_negation_fn(const relation_base & t, 
            const relation_base & negated_obj, unsigned joined_col_cnt, 
            const unsigned * t_cols, const unsigned * negated_cols);
    };


    // -----------------------------------
    //
    // sieve_relation
    //
    // -----------------------------------

    class sieve_relation : public relation_base {
        friend class sieve_relation_plugin;
        friend class sieve_relation_plugin::join_fn;
        friend class sieve_relation_plugin::transformer_fn;
        friend class sieve_relation_plugin::union_fn;
        friend class sieve_relation_plugin::filter_fn;

        svector<bool> m_inner_cols;

        unsigned_vector m_sig2inner;
        unsigned_vector m_inner2sig;
        unsigned_vector m_ignored_cols;  //in ascending order, so that it can be used in project-like functions

        scoped_rel<relation_base> m_inner;


        sieve_relation(sieve_relation_plugin & p, const relation_signature & s,
            const bool * inner_columns, relation_base * inner);

    public:
        sieve_relation_plugin & get_plugin() const { 
            return static_cast<sieve_relation_plugin &>(relation_base::get_plugin());
        }

        bool is_inner_col(unsigned idx) const { return m_sig2inner[idx]!=UINT_MAX; }
        unsigned get_inner_col(unsigned idx) const { 
            SASSERT(is_inner_col(idx));
            return m_sig2inner[idx];
        }
        bool no_sieved_columns() const { return m_ignored_cols.size()==0; }
        bool no_inner_columns() const { return m_ignored_cols.size()==get_signature().size(); }

        relation_base & get_inner() { return *m_inner; }
        const relation_base & get_inner() const { return *m_inner; }

        virtual void add_fact(const relation_fact & f);
        virtual bool contains_fact(const relation_fact & f) const;
        virtual sieve_relation * clone() const;
        virtual relation_base * complement(func_decl*p) const;
        virtual void to_formula(expr_ref& fml) const;

        virtual bool empty() const { return get_inner().empty(); }
        virtual void reset() { get_inner().reset(); }
        virtual unsigned get_size_estimate_rows() const { return get_inner().get_size_estimate_rows(); }
        virtual unsigned get_size_estimate_bytes() const { return get_inner().get_size_estimate_bytes(); }

        virtual void display(std::ostream & out) const;
    };


};

#endif /* _DL_SIEVE_RELATION_H_ */

