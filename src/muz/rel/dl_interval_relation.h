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
#ifndef _DL_INTERVAL_RELATION_H_
#define _DL_INTERVAL_RELATION_H_


#include "dl_context.h"
#include "dl_relation_manager.h"
#include "dl_base.h"
#include "old_interval.h"
#include "dl_vector_relation.h"
#include "arith_decl_plugin.h"
#include "basic_simplifier_plugin.h"

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
        virtual bool can_handle_signature(const relation_signature & s);
        static symbol get_name() { return symbol("interval_relation"); }
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

        virtual void add_fact(const relation_fact & f);
        virtual bool contains_fact(const relation_fact & f) const;
        virtual interval_relation * clone() const;
        virtual interval_relation * complement(func_decl*) const;
        virtual void to_formula(expr_ref& fml) const;
        interval_relation_plugin& get_plugin() const; 

        void filter_interpreted(app* cond);
        virtual bool is_precise() const { return false; }

    private:

        virtual interval mk_intersect(interval const& t1, interval const& t2, bool& is_empty) const { 
            return get_plugin().meet(t1, t2, is_empty); 
        }

        virtual interval mk_unite(interval const& t1, interval const& t2) const { return get_plugin().unite(t1,t2); }

        virtual interval mk_widen(interval const& t1, interval const& t2) const { return get_plugin().widen(t1,t2); }

        virtual bool is_subset_of(interval const& t1, interval const& t2) const { NOT_IMPLEMENTED_YET(); return false; }

        virtual bool is_full(interval const& t) const { 
            return interval_relation_plugin::is_infinite(t);
        }

        virtual bool is_empty(unsigned idx, interval const& t) const {
            return interval_relation_plugin::is_empty(idx, t);
        }

        virtual void mk_rename_elem(interval& i, unsigned col_cnt, unsigned const* cycle);

        virtual void display_index(unsigned idx, interval const & i, std::ostream& out) const;

        void mk_intersect(unsigned idx, interval const& i);

    };
        
};

#endif 

