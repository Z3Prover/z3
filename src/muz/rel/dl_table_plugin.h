/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    dl_table_plugin.h

Abstract:

    <abstract>

Author:

    Krystof Hoder (t-khoder) 2010-09-23.

Revision History:

--*/
#pragma once

#include "ast/ast.h"
#include "util/map.h"
#include "util/vector.h"

#include"dl_table_ops.h"

namespace datalog {

    /**
       Termplate class containing common infrastructure for relations and tables
    */
    template<class Traits>
    struct tr_infrastructure {

        typedef typename Traits::base_object base_object;
        typedef typename Traits::signature signature;
        typedef typename Traits::element element;
        typedef typename Traits::fact fact;
        typedef typename Traits::kind kind;

        class base_fn {
        public:
            virtual ~base_fn() {}
        };

        class join_fn : public base_fn {
        public:
            virtual base_object * operator()(const base_object & t1, const base_object & t2);
        };

        class transformer_fn : public base_fn {
        public:
            virtual base_object * operator()(const base_object & t);
        };

        class union_fn : public base_fn {
        public:
            virtual void operator()(base_object & tgt, const base_object & src, base_object * delta);
        };

        class mutator_fn : public base_fn {
        public:
            virtual void operator()(base_object & t);
        };

        class negation_filter_fn : public base_fn {
        public:
            virtual void operator()(base_object & t, const base_object & negated_obj);
        };

        class plugin_object {
            const kind m_kind;
        protected:
            plugin_object(kind k) : m_kind(k) {}
        public:
            kind get_kind();

            virtual base_object * mk_empty(const signature & s) = 0;

            virtual join_fn * mk_join_fn(const table_base & t1, const table_base & t2,
                unsigned col_cnt, const unsigned * cols1, const unsigned * cols2) {
                NOT_IMPLEMENTED_YET();
            }

            virtual transformer_fn * mk_project_fn(const base_object & t, unsigned col_cnt, 
                const unsigned * removed_cols) = 0

            virtual transformer_fn * mk_rename_fn(const base_object & t, unsigned permutation_cycle_len, 
                const unsigned * permutation_cycle) = 0;

            virtual union_fn * mk_union_fn(base_object & tgt, const base_object & src, base_object * delta) = 0;

            virtual mutator_fn * mk_filter_identical_fn(base_object & t, unsigned col_cnt, 
                const unsigned * identical_cols) = 0;

            virtual mutator_fn * mk_filter_equal_fn(base_object & t, const element & value, 
                unsigned col) = 0;

            virtual mutator_fn * mk_filter_interpreted_fn(base_object & t, app * condition) = 0;

            virtual negation_filter_fn * mk_filter_interpreted_fn(base_object & t, 
                const base_object & negated_obj, unsigned joined_col_cnt, 
                const unsigned * t_cols, const unsigned * negated_cols) = 0;

        };

        class base_ancestor {
            const kind m_kind;
        protected:
            relation_manager & m_manager;
            signature m_signature;

            base_ancestor(kind k, relation_manager & m, const signature & s) 
                : m_kind(k), m_manager(m), m_signature(s) {}
        public:
            virtual ~base_ancestor() {}

            kind get_kind() const { return m_kind; }
            relation_manager & get_manager() const { return m_manager; }
            const signature & get_signature() const { return m_signature; }

            virtual bool empty() const = 0;
            virtual void add_fact(const fact & f) = 0;
            virtual bool contains_fact(const fact & f) const = 0;

            /**
               \brief Return table that contains the same data as the current one.
            */
            virtual base_object * clone() const;

        };
    };


    // -----------------------------------
    //
    // relation_base
    //
    // -----------------------------------

    class relation_base1;

    enum relation_kind {
        RK_UNKNOWN,
        RK_TABLE
    };

    struct relation_traits {
        typedef relation_base1 base_object;
        typedef relation_signature signature;
        typedef app * element;
        typedef ptr_vector<app> fact;
        typedef relation_kind kind;
    };

    typedef tr_infrastructure<relation_traits> relation_infrastructure;

    typedef relation_infrastructure::plugin_object relation_plugin_base;

    class relation_base1 : public relation_infrastructure::base_ancestor {

    };


    // -----------------------------------
    //
    // table_base
    //
    // -----------------------------------
    
    class table_base1;

    struct table_traits {
        typedef table_base1 base_object;
        typedef table_signature signature;
        typedef unsigned element;
        typedef unsigned_vector fact;
        typedef table_kind kind;
    };

    typedef tr_infrastructure<table_traits> table_infrastructure;

    typedef table_infrastructure::plugin_object table_plugin_base;

    class table_base1 : public table_infrastructure::base_ancestor {

    };

};


