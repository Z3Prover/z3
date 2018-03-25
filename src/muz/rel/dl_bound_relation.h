/*++
Copyright (c) 2010 Microsoft Corporation

Module Name:

    dl_bound_relation.h

Abstract:

    Basic (strict upper) bound relation.

Author:

    Nikolaj Bjorner (nbjorner) 2010-2-11

Revision History:

--*/
#ifndef DL_BOUND_RELATION_H_
#define DL_BOUND_RELATION_H_

#include "muz/base/dl_context.h"
#include "muz/rel/dl_relation_manager.h"
#include "muz/rel/dl_base.h"
#include "util/uint_set.h"
#include "muz/rel/dl_vector_relation.h"
#include "muz/rel/dl_interval_relation.h"
#include "ast/arith_decl_plugin.h"
#include "ast/rewriter/bool_rewriter.h"

namespace datalog {

    class bound_relation; 

    class bound_relation_plugin : public relation_plugin {
        friend class bound_relation;
        class join_fn;
        class project_fn;
        class rename_fn;
        class union_fn;
        class union_fn_i;
        class filter_equal_fn;
        class filter_identical_fn;
        class filter_interpreted_fn;
        class filter_intersection_fn;
        arith_util m_arith;
        bool_rewriter m_bsimp;
    public:
        bound_relation_plugin(relation_manager& m);
        bool can_handle_signature(const relation_signature & s) override;
        static symbol get_name() { return symbol("bound_relation"); }
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

        relation_join_fn * mk_join_project_fn(const relation_base & t1, const relation_base & t2,
                    unsigned joined_col_cnt, const unsigned * cols1, const unsigned * cols2,
                    unsigned removed_col_cnt, const unsigned * removed_cols) override { return nullptr; }


#if 0
        virtual intersection_filter_fn * mk_filter_by_intersection_fn(
            const relation_base & t, 
            const relation_base & src, unsigned joined_col_cnt, 
            const unsigned * t_cols, const unsigned * src_cols) {
            return 0;
        }
#endif

        static bound_relation* get(relation_base* r);
    private:
        static bound_relation& get(relation_base& r);
        static bound_relation const & get(relation_base const& r);
        

        static bool is_interval_relation(relation_base const& r);
        static interval_relation& get_interval_relation(relation_base& r);
        static interval_relation const& get_interval_relation(relation_base const& r);
    };

    struct uint_set2 {
        uint_set lt;
        uint_set le;
        uint_set2(uint_set2 const& other):lt(other.lt), le(other.le) {}
        uint_set2() {}
        bool operator==(const uint_set2& other) const {
            return other.lt == lt && other.le == le;
        }
        bool operator!=(const uint_set2& other) const {
            return other.lt != lt || other.le != le;
        }
    };

    inline std::ostream & operator<<(std::ostream & target, const uint_set2 & s) {
        return target << s.lt << " " << s.le;
    }


    class bound_relation_helper {
    public:
        static void mk_project_t(uint_set2& t, unsigned_vector const& renaming);
    };

    class bound_relation : public vector_relation<uint_set2, bound_relation_helper> {
        friend class bound_relation_plugin;
        svector<std::pair<unsigned, bool> > m_todo;        

    public:
        bound_relation(bound_relation_plugin& p, relation_signature const& s, bool is_empty);
        bound_relation& operator=(bound_relation const& other);

        bool empty() const override { return m_empty; }
        void add_fact(const relation_fact & f) override;
        bool contains_fact(const relation_fact & f) const override;
        bound_relation * clone() const override;
        bound_relation * complement(func_decl* p) const override;
        void to_formula(expr_ref& fml) const override;
        bound_relation_plugin& get_plugin() const; 

        void mk_union_i(interval_relation const& src, bound_relation* delta, bool is_widen);

        void mk_lt(unsigned i, unsigned j);

        void mk_lt(unsigned i);

        void mk_le(unsigned i, unsigned j);

        bool is_lt(unsigned i, unsigned j) const;

        bool is_precise() const override { return false; }

    private:
        typedef uint_set2 T;
        T mk_intersect(T const& t1, T const& t2, bool& is_empty) const override;

        T mk_widen(T const& t1, T const& t2) const override;

        T mk_unite(T const& t1, T const& t2) const override;

        T mk_eq(union_find<> const& old_eqs, union_find<> const& new_eqs, T const& t) const override;

        void mk_rename_elem(T& i, unsigned col_cnt, unsigned const* cycle) override;


        bool is_subset_of(T const& t1, T const& t2) const override;

        bool is_full(T const& t) const override;

        bool is_empty(unsigned idx, T const& t) const override;

        void display_index(unsigned idx, T const& t, std::ostream& out) const override;

        void normalize(T const& src, T& dst) const;

        void normalize(uint_set const& src, uint_set& dst) const;


       
    };
        
};

#endif 

