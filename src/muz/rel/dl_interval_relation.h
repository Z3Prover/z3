/*++
Copyright (c) 2010 Microsoft Corporation

Module Name:

    dl_interval_relation.h

Abstract:

    Basic interval reatlion.

Author:

    Nikolaj Bjorner (nbjorner) 2010-2-11

Revision History:

--*/
#pragma once


#include "ast/arith_decl_plugin.h"
#include "smt/old_interval.h"
#include "muz/base/dl_context.h"
#include "muz/rel/dl_relation_manager.h"
#include "muz/rel/dl_base.h"
#include "muz/rel/dl_vector_relation.h"

namespace datalog {

    class interval_relation;

    class interval_relation_plugin : public relation_plugin {
        v_dependency_manager m_dep;
        interval             m_empty;
        arith_util           m_arith;

        class join_fn;
        class project_fn;
        class rename_fn;
        class union_fn;
        class filter_equal_fn;
        class filter_identical_fn;
        class filter_interpreted_fn;
        friend class interval_relation;
       
        interval unite(interval const& src1, interval const& src2);
        interval widen(interval const& src1, interval const& src2);
        interval meet(interval const& src1, interval const& src2, bool& is_empty);

        v_dependency_manager & dep() const { return const_cast<v_dependency_manager&>(m_dep); }

    public:
        interval_relation_plugin(relation_manager& m);
        bool can_handle_signature(const relation_signature & s) override;
        static symbol get_name() { return symbol("interval_relation"); }
        relation_base * mk_empty(const relation_signature & s) override;
        relation_base * mk_full(func_decl* p, const relation_signature & s) override;
        relation_join_fn * mk_join_fn(const relation_base & t1, const relation_base & t2,
            unsigned col_cnt, const unsigned * cols1, const unsigned * cols2) override;
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

        static bool is_empty(unsigned idx, interval const& i);
        static bool is_infinite(interval const& i);

    private:
        static interval_relation& get(relation_base& r);
        static interval_relation const & get(relation_base const& r);   

        bool is_linear(expr* e, unsigned& pos, unsigned& neg, rational& k, bool is_pos) const;

        // x + k <= y
        bool is_le(app* cond, unsigned& x, rational& k, unsigned& y, bool& is_int) const;
        // x + k < y
        bool is_lt(app* cond, unsigned& x, rational& k, unsigned& y) const;
        // x + k = y
        bool is_eq(app* cond, unsigned& x, rational& k, unsigned& y) const;
    };

    
    class interval_relation : public vector_relation<interval> {              
        friend class interval_relation_plugin;
        friend class interval_relation_plugin::filter_equal_fn;
    public:
        interval_relation(interval_relation_plugin& p, relation_signature const& s, bool is_empty);

        void add_fact(const relation_fact & f) override;
        bool contains_fact(const relation_fact & f) const override;
        interval_relation * clone() const override;
        interval_relation * complement(func_decl*) const override;
        void to_formula(expr_ref& fml) const override;
        interval_relation_plugin& get_plugin() const; 

        void filter_interpreted(app* cond);
        bool is_precise() const override { return false; }

    private:

        interval mk_intersect(interval const& t1, interval const& t2, bool& is_empty) const override {
            return get_plugin().meet(t1, t2, is_empty); 
        }

        interval mk_unite(interval const& t1, interval const& t2) const override { return get_plugin().unite(t1,t2); }

        interval mk_widen(interval const& t1, interval const& t2) const override { return get_plugin().widen(t1,t2); }

        bool is_subset_of(interval const& t1, interval const& t2) const override { NOT_IMPLEMENTED_YET(); return false; }

        bool is_full(interval const& t) const override {
            return interval_relation_plugin::is_infinite(t);
        }

        bool is_empty(unsigned idx, interval const& t) const override {
            return interval_relation_plugin::is_empty(idx, t);
        }

        void mk_rename_elem(interval& i, unsigned col_cnt, unsigned const* cycle) override;

        void display_index(unsigned idx, interval const & i, std::ostream& out) const override;

        void mk_intersect(unsigned idx, interval const& i);

    };
        
};


