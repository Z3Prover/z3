/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    dl_lazy_table.h

Abstract:

    Structure for delaying table operations.
    

Author:

    Nikolaj Bjorner (nbjorner) 2013-09-04

Revision History:

--*/

#ifndef DL_LAZY_TABLE_H_
#define DL_LAZY_TABLE_H_

#include "muz/rel/dl_base.h"
#include "util/ref.h"

namespace datalog {
    
    class lazy_table;
    
    class lazy_table_plugin : public table_plugin {
        friend class lazy_table;
        class join_fn;
        class project_fn;
        class union_fn;
        class rename_fn;
        class filter_equal_fn;
        class filter_identical_fn;
        class filter_interpreted_fn;
        class filter_by_negation_fn;
        
        table_plugin& m_plugin;
        
        static symbol mk_name(table_plugin& p);
        
    public:
        lazy_table_plugin(table_plugin& p): 
            table_plugin(mk_name(p), p.get_manager()), 
            m_plugin(p) {}
        
        bool can_handle_signature(const table_signature & s) override {
            return m_plugin.can_handle_signature(s);
        } 
        
        table_base * mk_empty(const table_signature & s) override;
                
        static table_plugin* mk_sparse(relation_manager& rm);
        
    protected:
        table_join_fn * mk_join_fn(
            const table_base & t1, const table_base & t2,
            unsigned col_cnt, const unsigned * cols1, const unsigned * cols2) override;
        table_union_fn * mk_union_fn(
            const table_base & tgt, const table_base & src,
            const table_base * delta) override;
        table_transformer_fn * mk_project_fn(
            const table_base & t, unsigned col_cnt,
            const unsigned * removed_cols) override;
        table_transformer_fn * mk_rename_fn(
            const table_base & t, unsigned permutation_cycle_len,
            const unsigned * permutation_cycle) override;
        table_mutator_fn * mk_filter_identical_fn(
            const table_base & t, unsigned col_cnt, const unsigned * identical_cols) override;
        table_mutator_fn * mk_filter_equal_fn(
            const table_base & t, const table_element & value, unsigned col) override;
        table_mutator_fn * mk_filter_interpreted_fn(
            const table_base & t, app * condition) override;
        table_intersection_filter_fn * mk_filter_by_negation_fn(
            const table_base & t,
            const table_base & negated_obj, unsigned joined_col_cnt,
            const unsigned * t_cols, const unsigned * negated_cols) override;

        static lazy_table const& get(table_base const& tb);
        static lazy_table& get(table_base& tb);
        static lazy_table const* get(table_base const* tb);
        static lazy_table* get(table_base* tb);           
    };

    enum lazy_table_kind {
        LAZY_TABLE_BASE,
        LAZY_TABLE_JOIN,
        LAZY_TABLE_PROJECT,
        LAZY_TABLE_RENAME,
        LAZY_TABLE_FILTER_IDENTICAL,
        LAZY_TABLE_FILTER_EQUAL,
        LAZY_TABLE_FILTER_INTERPRETED,
        LAZY_TABLE_FILTER_BY_NEGATION
    };

    class lazy_table_ref {
    protected:
        lazy_table_plugin&     m_plugin;
        table_signature        m_signature;
        unsigned               m_ref;
        scoped_rel<table_base> m_table;
        relation_manager&  rm() { return m_plugin.get_manager(); }
        virtual table_base* force() = 0;
    public:
        lazy_table_ref(lazy_table_plugin& p, table_signature const& sig): 
            m_plugin(p), m_signature(sig), m_ref(0) {}
        virtual ~lazy_table_ref() {}
        void inc_ref() { ++m_ref; }
        void dec_ref() { --m_ref; if (0 == m_ref) dealloc(this);  }
        void release_table() { m_table.release(); }

        virtual lazy_table_kind kind() const = 0;
        table_signature const& get_signature() const { return m_signature; }
        lazy_table_plugin & get_lplugin() const { return m_plugin; }
        table_base* eval() { if (!m_table) { m_table = force(); } SASSERT(m_table); return m_table.get(); }
    };

    class lazy_table : public table_base {
    protected:
        mutable ref<lazy_table_ref> m_ref;

    public:
        lazy_table(lazy_table_ref* t):
            table_base(t->get_lplugin(), t->get_signature()), 
            m_ref(t)
        {}

        ~lazy_table() override {}

        lazy_table_plugin& get_lplugin() const { 
            return dynamic_cast<lazy_table_plugin&>(table_base::get_plugin()); 
        }

        table_base * clone() const override;
        table_base * complement(func_decl* p, const table_element * func_columns = nullptr) const override;
        bool empty() const override;
        bool contains_fact(const table_fact & f) const override;
        void remove_fact(table_element const* fact) override;
        void remove_facts(unsigned fact_cnt, const table_fact * facts) override;
        void remove_facts(unsigned fact_cnt, const table_element * facts) override;
        void reset() override;
        void add_fact(table_fact const& f) override;
       
        unsigned get_size_estimate_rows() const override { return 1; }
        unsigned get_size_estimate_bytes() const override { return 1; }
        bool knows_exact_size() const override { return false; }

        table_base* eval() const;

        table_base::iterator begin() const override;
        table_base::iterator end() const override;

        lazy_table_ref* get_ref() const { return m_ref.get(); }
        void set(lazy_table_ref* r) { m_ref = r; }
    };

    class lazy_table_base : public lazy_table_ref {
    public:
        lazy_table_base(lazy_table_plugin & p, table_base* table)
            : lazy_table_ref(p, table->get_signature()) {
            m_table = table;
            // SASSERT(&p.m_plugin == &table->get_lplugin());
        }
        ~lazy_table_base() override {}
        lazy_table_kind kind() const override { return LAZY_TABLE_BASE; }
        table_base* force() override { return m_table.get(); }
    };

    class lazy_table_join : public lazy_table_ref {
        unsigned_vector m_cols1;
        unsigned_vector m_cols2;
        ref<lazy_table_ref>     m_t1;
        ref<lazy_table_ref>     m_t2;
    public:
        lazy_table_join(unsigned col_cnt, 
                        const unsigned * cols1, const unsigned * cols2, 
                        lazy_table const& t1, lazy_table const& t2, table_signature const& sig) 
            : lazy_table_ref(t1.get_lplugin(), sig), 
              m_cols1(col_cnt, cols1), 
              m_cols2(col_cnt, cols2),
              m_t1(t1.get_ref()),
              m_t2(t2.get_ref()) { }
        ~lazy_table_join() override {}
        lazy_table_kind kind() const override { return LAZY_TABLE_JOIN; }
        unsigned_vector const& cols1() const { return m_cols1; }
        unsigned_vector const& cols2() const { return m_cols2; }
        lazy_table_ref* t1() const { return m_t1.get(); }
        lazy_table_ref* t2() const { return m_t2.get(); }
        table_base* force() override;
    };


    class lazy_table_project : public lazy_table_ref {
        unsigned_vector         m_cols;
        ref<lazy_table_ref>     m_src;
    public:
        lazy_table_project(unsigned col_cnt, const unsigned * cols, lazy_table const& src, table_signature const& sig)
            : lazy_table_ref(src.get_lplugin(), sig), 
              m_cols(col_cnt, cols), 
              m_src(src.get_ref()) {}
        ~lazy_table_project() override {}
        
        lazy_table_kind kind() const override { return LAZY_TABLE_PROJECT; }
        unsigned_vector const& cols() const { return m_cols; }
        lazy_table_ref* src() const { return m_src.get(); }
        table_base* force() override;
    };

    class lazy_table_rename : public lazy_table_ref {
        unsigned_vector         m_cols;
        ref<lazy_table_ref>     m_src;
    public:
        lazy_table_rename(unsigned col_cnt, const unsigned * cols, lazy_table const& src, table_signature const& sig)
            : lazy_table_ref(src.get_lplugin(), sig), 
              m_cols(col_cnt, cols), 
              m_src(src.get_ref()) {}
        ~lazy_table_rename() override {}
        
        lazy_table_kind kind() const override { return LAZY_TABLE_RENAME; }
        unsigned_vector const& cols() const { return m_cols; }
        lazy_table_ref* src() const { return m_src.get(); }
        table_base* force() override;
    };

    class lazy_table_filter_identical : public lazy_table_ref {
        unsigned_vector          m_cols;
        ref<lazy_table_ref>      m_src;
    public:
        lazy_table_filter_identical(unsigned col_cnt, const unsigned * cols, lazy_table const& src)
            : lazy_table_ref(src.get_lplugin(), src.get_signature()), m_cols(col_cnt, cols), m_src(src.get_ref()) {}
        ~lazy_table_filter_identical() override {}
        
        lazy_table_kind kind() const override { return LAZY_TABLE_FILTER_IDENTICAL; }
        unsigned_vector const& cols() const { return m_cols; }
        lazy_table_ref* src() const { return m_src.get(); }
        table_base* force() override;
    };

    class lazy_table_filter_equal : public lazy_table_ref {
        unsigned                  m_col;
        table_element             m_value;
        ref<lazy_table_ref>       m_src;
    public:
        lazy_table_filter_equal(unsigned col, table_element value, lazy_table const& src)
            : lazy_table_ref(src.get_lplugin(), src.get_signature()), 
            m_col(col), 
            m_value(value), 
            m_src(src.get_ref()) {}
        ~lazy_table_filter_equal() override {}
        
        lazy_table_kind kind() const override { return LAZY_TABLE_FILTER_EQUAL; }
        unsigned        col() const { return m_col; }
        table_element   value() const { return m_value; }
        lazy_table_ref* src() const { return m_src.get(); }
        table_base* force() override;
    };

    class lazy_table_filter_interpreted : public lazy_table_ref {
        app_ref                  m_condition;
        ref<lazy_table_ref>      m_src;
    public:
        lazy_table_filter_interpreted(lazy_table const& src, app* condition)
            : lazy_table_ref(src.get_lplugin(), src.get_signature()), 
              m_condition(condition, src.get_lplugin().get_ast_manager()), m_src(src.get_ref()) {}
        ~lazy_table_filter_interpreted() override {}
        
        lazy_table_kind kind() const override { return LAZY_TABLE_FILTER_INTERPRETED; }
        app* condition() const { return m_condition; }        
        lazy_table_ref* src() const { return m_src.get(); }
        table_base* force() override;
    };


    class lazy_table_filter_by_negation : public lazy_table_ref {
        ref<lazy_table_ref>       m_tgt;
        ref<lazy_table_ref>       m_src;
        unsigned_vector           m_cols1;
        unsigned_vector           m_cols2;
    public:
        lazy_table_filter_by_negation(lazy_table const& tgt, lazy_table const& src, 
                                      unsigned_vector const& c1, unsigned_vector const& c2) 
        : lazy_table_ref(tgt.get_lplugin(), tgt.get_signature()),
            m_tgt(tgt.get_ref()), 
            m_src(src.get_ref()), 
            m_cols1(c1),
            m_cols2(c2) {}
        ~lazy_table_filter_by_negation() override {}
        lazy_table_kind kind() const override { return LAZY_TABLE_FILTER_BY_NEGATION; }
        lazy_table_ref* tgt() const { return m_tgt.get(); }
        lazy_table_ref* src() const { return m_src.get(); }
        unsigned_vector const& cols1() const { return m_cols1; }
        unsigned_vector const& cols2() const { return m_cols2; }
        table_base* force() override;
    };


}

#endif 
