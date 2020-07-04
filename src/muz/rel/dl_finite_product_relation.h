/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    dl_finite_product_relation.h

Abstract:

    <abstract>

Author:

    Krystof Hoder (t-khoder) 2010-09-24.

Revision History:

--*/
#pragma once


#include "muz/rel/dl_base.h"
#include "muz/rel/dl_relation_manager.h"
#include "muz/rel/dl_table_relation.h"

namespace datalog {

    class finite_product_relation;

    void universal_delete(finite_product_relation* ptr);


    class finite_product_relation_plugin : public relation_plugin {
        friend class finite_product_relation;
    public:
        struct rel_spec {
            family_id m_inner_kind; //null_family_id means we don't care about the kind
            bool_vector m_table_cols;

            rel_spec() : m_inner_kind(null_family_id) {}
            rel_spec(const bool_vector& table_cols) 
                : m_inner_kind(null_family_id), m_table_cols(table_cols) {}

            bool operator==(const rel_spec & o) const {
                return m_inner_kind==o.m_inner_kind && vectors_equal(m_table_cols, o.m_table_cols);
            }
            struct hash {
                unsigned operator()(const rel_spec & o) const {
                    return o.m_inner_kind^svector_hash<bool_hash>()(o.m_table_cols);
                }
            };
        };
    private:

        class join_fn;
        class converting_join_fn;
        class project_fn;
        class rename_fn;
        class union_fn;
        class inner_singleton_union_fn;
        class converting_union_fn;
        class filter_identical_fn;
        class filter_equal_fn;
        class filter_interpreted_fn;
        class negation_filter_fn;
        class filter_identical_pairs_fn;

        relation_plugin & m_inner_plugin;

        rel_spec_store<rel_spec, rel_spec::hash, default_eq<rel_spec> > m_spec_store;

        static symbol get_name(relation_plugin & inner_plugin);
        family_id get_relation_kind(finite_product_relation & r, const bool * table_columns);

        static void get_all_possible_table_columns(relation_manager & rmgr, const relation_signature & s, 
            bool_vector & table_columns);
        void get_all_possible_table_columns(const relation_signature & s, bool_vector & table_columns) {
            get_all_possible_table_columns(get_manager(), s, table_columns);
        }

        void split_signatures(const relation_signature & s, table_signature & table_sig, 
            relation_signature & remaining_sig);
        void split_signatures(const relation_signature & s, const bool * table_columns, 
            table_signature & table_sig, relation_signature & remaining_sig);
    public:
        static finite_product_relation & get(relation_base & r);
        static const finite_product_relation & get(const relation_base & r);
        static finite_product_relation * get(relation_base * r);
        static const finite_product_relation * get(const relation_base * r);

        static finite_product_relation_plugin & get_plugin(relation_manager & rmgr, relation_plugin & inner);

        finite_product_relation_plugin(relation_plugin & inner_plugin, relation_manager & manager);

        void initialize(family_id fid) override;

        relation_plugin & get_inner_plugin() const { return m_inner_plugin; }

        bool can_handle_signature(const relation_signature & s) override;

        relation_base * mk_empty(const relation_signature & s) override;
        /**
           \c inner_kind==null_family_id means we don't care about the kind of the inner relation
        */
        finite_product_relation * mk_empty(const relation_signature & s, const bool * table_columns,
            family_id inner_kind=null_family_id);
        finite_product_relation * mk_empty(const finite_product_relation & original);
        relation_base * mk_empty(const relation_base & original) override;
        relation_base * mk_empty(const relation_signature & s, family_id kind) override;

        relation_base * mk_full(func_decl* p, const relation_signature & s) override;

        /**
           \brief Return true if \c r can be converted to \c finite_product_relation_plugin either
           by \c mk_from_table_relation or by \c mk_from_inner_relation.
        */
        bool can_be_converted(const relation_base & r);

        /**
           If the conversion cannot be performed, 0 is returned.
        */
        finite_product_relation * mk_from_table_relation(const table_relation & r);
        finite_product_relation * mk_from_inner_relation(const relation_base & r);

        bool can_convert_to_table_relation(const finite_product_relation & r);
        table_relation * to_table_relation(const finite_product_relation & r);

    protected:
        relation_join_fn * mk_join_fn(const relation_base & t1, const relation_base & t2,
            unsigned col_cnt, const unsigned * cols1, const unsigned * cols2) override;
        relation_transformer_fn * mk_project_fn(const relation_base & t, unsigned col_cnt,
            const unsigned * removed_cols) override;
        relation_transformer_fn * mk_rename_fn(const relation_base & t, unsigned permutation_cycle_len,
            const unsigned * permutation_cycle) override;
        relation_union_fn * mk_union_fn(const relation_base & tgt, const relation_base & src,
            const relation_base * delta) override;
        relation_mutator_fn * mk_filter_identical_fn(const relation_base & t, unsigned col_cnt,
            const unsigned * identical_cols) override;
        relation_mutator_fn * mk_filter_equal_fn(const relation_base & t, const relation_element & value,
            unsigned col) override;
        relation_mutator_fn * mk_filter_interpreted_fn(const relation_base & t, app * condition) override;
        relation_intersection_filter_fn * mk_filter_by_negation_fn(const relation_base & t,
            const relation_base & negated_obj, unsigned joined_col_cnt,
            const unsigned * t_cols, const unsigned * negated_cols) override;

    private:
        /**
           \brief Create a filter that enforces equality between pairs of table and relation columns

           The column numbers in arrays \c table_cols and \c rel_cols must be local to the table/inner relation.
        */
        relation_mutator_fn * mk_filter_identical_pairs(const finite_product_relation & r, unsigned col_cnt, 
            const unsigned * table_cols, const unsigned * rel_cols);

        /**
           \brief Create a join-project operation that creates a table according to \c relation_table
           but with references to relations updated and removed according to the content of \c filtered_table.
           \c selected_columns contains sorted indexes of data columns in \c relation_table that are also in 
           the \c filtered_table (so that the first column in \c filtered_table corresponds to 
           \c selected_columns[0] -th column in \c relation_table etc...)

           Signature of \c relation_table:
           (data columns)(functional column with indexes of relation objects)

           Signature of \c filtered_table:
           (selected data columns)(non-functional column with original relation object indexes)
                (functional column with indexes of filtered relation objects)

        */
        static table_join_fn * mk_assembler_of_filter_result(const table_base & relation_table, 
                const table_base & filtered_table, const unsigned_vector & selected_columns);

    };

    class finite_product_relation : public relation_base {
        friend class finite_product_relation_plugin;
        friend class finite_product_relation_plugin::join_fn;
        friend class finite_product_relation_plugin::project_fn;
        friend class finite_product_relation_plugin::union_fn;
        friend class finite_product_relation_plugin::rename_fn;
        friend class finite_product_relation_plugin::inner_singleton_union_fn;
        friend class finite_product_relation_plugin::filter_equal_fn;
        friend class finite_product_relation_plugin::filter_identical_pairs_fn;

        class live_rel_collection_reducer;


    public:
        /**
            Size of this sort determines how many different relation objects can we refer to.
        */
        static const table_sort s_rel_idx_sort;


        /**
           \brief The last column in the signature is a functional column with index of the
           associated inner relation. The other columns correspond to the relation signature
           according to \c m_table2sig.

           It holds that \c m_table_sig.size()-1==m_table2sig.size()
         */

        table_signature m_table_sig;
        unsigned_vector m_table2sig; // (ordered list)
        unsigned_vector m_sig2table; //index of corresponding table column or UINT_MAX
    private:
        relation_signature m_other_sig;
        unsigned_vector m_other2sig; // (ordered list)
    public:
        unsigned_vector m_sig2other; //index of corresponding other relation column or UINT_MAX
    private:
        relation_plugin & m_other_plugin;
        family_id m_other_kind;

        mutable table_base * m_table;
    public:
        mutable relation_vector m_others;
    private:
        mutable unsigned_vector m_available_rel_indexes;

        /**
           \c UINT_MAX means uninitialized.
           If we can get away with it, we want to have a single full relation to refer to.
         */
        mutable unsigned m_full_rel_idx;

        mutable idx_set m_live_rel_collection_acc;
        mutable scoped_ptr<table_transformer_fn> m_live_rel_collection_project;

        mutable scoped_ptr<table_intersection_filter_fn> m_empty_rel_removal_filter;

        void recycle_rel_idx(unsigned idx) const;

        // creates a full relation if it does not exist.
        unsigned get_full_rel_idx(); 



    public:
        relation_base & get_inner_rel(table_element idx) 
        { SASSERT(idx<UINT_MAX); return get_inner_rel(static_cast<unsigned>(idx)); }
        relation_base & get_inner_rel(unsigned idx) { SASSERT(m_others[idx]); return *m_others[idx]; }
        const relation_base & get_inner_rel(unsigned idx) const 
        { return const_cast<finite_product_relation &>(*this).get_inner_rel(idx); }

        unsigned get_next_rel_idx() const;

        /**
           The relation takes ownership of the \c inner object.
        */
        void set_inner_rel(table_element idx, relation_base * inner)
        { SASSERT(idx<UINT_MAX); return set_inner_rel(static_cast<unsigned>(idx), inner); }
        /**
           The relation takes ownership of the \c inner object.
        */
        void set_inner_rel(unsigned idx, relation_base * inner) {
            SASSERT(!m_others[idx]);
            SASSERT(inner);
            m_others[idx] = inner;
        }
        table_base & get_table() { return *m_table; }

        table_plugin & get_table_plugin() const { return get_table().get_plugin(); }

        void garbage_collect(bool remove_empty) const;

        /**
           \brief Initialize an empty relation with table \c table_vals and relations in \c others.

           The relation object takes ownership of relations inside the \c others vector.

           If \c contiguous is true, it can be assumed that there are no zero elements in the \c others array.
        */
        void init(const table_base & table_vals, const relation_vector & others, bool contiguous);

    private:


        /**
           \brief Extract the values of table non-functional columns from the relation fact.
           The value of the functional column which determines index of the inner relation is undefined.
         */
        void extract_table_fact(const relation_fact & rf, table_fact & tf) const;
        /**
           \brief Extract the values of the inner relation columns from the relation fact.
         */
        void extract_other_fact(const relation_fact & rf, relation_fact & of) const;

        relation_base * mk_empty_inner();
        relation_base * mk_full_inner(func_decl* pred);


        void complement_self(func_decl* pred);

        void collect_live_relation_indexes(idx_set & res) const;


        /**
           \brief Try to modify relations in \c rels so that they have the same columns corresponding to the table
           and the inner relation (so that the union can be perofrmed on theim in a straightforward way).

           Relations in \c rels must all have equal signature.

           Even if the function fails and false is returned, some relations may already be modified. They are
           in a valid state, but with different specification.
        */
        static bool try_unify_specifications(ptr_vector<finite_product_relation> & rels);

        bool try_modify_specification(const bool * table_cols);

        bool can_swap(const relation_base & r) const override
        { return &get_plugin()==&r.get_plugin(); }

        /**
           \brief Swap content of the current relation with the content of \c r.

           Both relations must come from the same plugin and be of the same signature.
        */
        void swap(relation_base & r) override;

        /**
           \brief Create a \c finite_product_relation object.
        */
        finite_product_relation(finite_product_relation_plugin & p, const relation_signature & s,
            const bool * table_columns, table_plugin & tplugin, relation_plugin & oplugin, family_id other_kind);
        finite_product_relation(const finite_product_relation & r);
        ~finite_product_relation() override;
    public:
        context & get_context() const;
        finite_product_relation_plugin & get_plugin() const { 
            return static_cast<finite_product_relation_plugin &>(relation_base::get_plugin());
        }

        bool is_table_column(unsigned col_idx) const { return m_sig2table[col_idx]!=UINT_MAX; }

        const table_base & get_table() const { return *m_table; }

        const relation_base & get_inner_rel(table_element idx) const
        { SASSERT(idx<UINT_MAX); return get_inner_rel(static_cast<unsigned>(idx)); }

        /**
           The function calls garbage_collect, so the internal state may change when it is called.
        */
        bool empty() const override;
        void reset() override { m_table->reset(); garbage_collect(false); }

        void add_fact(const relation_fact & f) override;
        bool contains_fact(const relation_fact & f) const override;

        finite_product_relation * clone() const override;
        finite_product_relation * complement(func_decl* p) const override;

        void display(std::ostream & out) const override;
        void display_tuples(func_decl & pred, std::ostream & out) const override;

        unsigned get_size_estimate_rows() const override { return m_table->get_size_estimate_rows(); }
        unsigned get_size_estimate_bytes() const override { return m_table->get_size_estimate_bytes(); }

        void to_formula(expr_ref& fml) const override;
    };

};


