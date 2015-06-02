/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    dl_relation_manager.h

Abstract:

    <abstract>

Author:

    Krystof Hoder (t-khoder) 2010-09-24.

Revision History:

--*/
#ifndef _DL_RELATION_MANAGER_H_
#define _DL_RELATION_MANAGER_H_


#include"map.h"
#include"vector.h"
#include"dl_base.h"

namespace datalog {

    class context;
    class dl_decl_util;
    class table_relation;
    class table_relation_plugin;
    class finite_product_relation;
    class finite_product_relation_plugin;
    class sieve_relation;
    class sieve_relation_plugin;
    class rule_set;


    class relation_manager {
        class empty_signature_relation_join_fn;
        class default_relation_join_project_fn;
        class default_relation_select_equal_and_project_fn;
        class default_relation_intersection_filter_fn;
        class default_relation_filter_interpreted_and_project_fn;
        class default_relation_apply_sequential_fn;

        class auxiliary_table_transformer_fn;
        class auxiliary_table_filter_fn;

        class default_table_join_fn;
        class default_table_project_fn;
        class null_signature_table_project_fn;
        class default_table_join_project_fn;
        class default_table_rename_fn;
        class default_table_union_fn;
        class default_table_filter_equal_fn;
        class default_table_filter_identical_fn;
        class default_table_filter_interpreted_fn;
        class default_table_filter_interpreted_and_project_fn;
        class default_table_negation_filter_fn;
        class default_table_filter_not_equal_fn;
        class default_table_select_equal_and_project_fn;
        class default_table_map_fn;
        class default_table_project_with_reduce_fn;

        typedef obj_map<func_decl, family_id> decl2kind_map;

        typedef u_map<relation_plugin *> kind2plugin_map;

        typedef map<const table_plugin *, table_relation_plugin *, ptr_hash<const table_plugin>, 
            ptr_eq<const table_plugin> > tp2trp_map;
        typedef map<const relation_plugin *, finite_product_relation_plugin *, ptr_hash<const relation_plugin>, 
            ptr_eq<const relation_plugin> > rp2fprp_map;

        typedef obj_map<func_decl, relation_base *> relation_map;
        typedef ptr_vector<table_plugin> table_plugin_vector;
        typedef ptr_vector<relation_plugin> relation_plugin_vector;

        context & m_context;
        table_plugin_vector m_table_plugins;
        relation_plugin_vector m_relation_plugins;
        //table_relation_plugins corresponding to table_plugins
        tp2trp_map m_table_relation_plugins;
        rp2fprp_map m_finite_product_relation_plugins;

        kind2plugin_map m_kind2plugin;

        table_plugin * m_favourite_table_plugin;

        relation_plugin * m_favourite_relation_plugin;

        relation_map m_relations;

        decl_set m_saturated_rels;

        family_id m_next_table_fid;
        family_id m_next_relation_fid;

        /**
           Map specifying what kind of relation should be used to represent particular predicate.
        */
        decl2kind_map m_pred_kinds;

        void register_relation_plugin_impl(relation_plugin * plugin);

        relation_manager(const relation_manager &); //private and undefined copy constructor
        relation_manager & operator=(const relation_manager &); //private and undefined operator=
    public:
        relation_manager(context & ctx) : 
          m_context(ctx), 
          m_favourite_table_plugin(0),
          m_favourite_relation_plugin(0),
          m_next_table_fid(0),
          m_next_relation_fid(0) {}

        virtual ~relation_manager();

        void reset();
        void reset_relations();

        context & get_context() const { return m_context; }
        dl_decl_util & get_decl_util() const;

        family_id get_next_table_fid() { return m_next_table_fid++; }
        family_id get_next_relation_fid(relation_plugin & claimer);


        /**
           Set what kind of relation is going to be used to represent the predicate \c pred.

           This function can be called only before the relation object for \c pred is created
           (i.e. before the \c get_relation function is called with \c pred as argument for the
           first time).
        */
        void set_predicate_kind(func_decl * pred, family_id kind);
        /**
           Return the relation kind that was requested to represent the predicate \c pred by 
           \c set_predicate_kind. If there was no such request, return \c null_family_id.
        */
        family_id get_requested_predicate_kind(func_decl * pred);
        relation_base & get_relation(func_decl * pred);
        relation_base * try_get_relation(func_decl * pred) const;
        /**
           \brief Store the relation \c rel under the predicate \c pred. The \c relation_manager
           takes over the relation object.
        */
        void store_relation(func_decl * pred, relation_base * rel);

        bool is_saturated(func_decl * pred) const { return m_saturated_rels.contains(pred); }
        void mark_saturated(func_decl * pred) { m_saturated_rels.insert(pred); }
        void reset_saturated_marks() { 
            if(!m_saturated_rels.empty()) {
                m_saturated_rels.reset();
            }
        }

        void collect_non_empty_predicates(decl_set & res) const;
        void restrict_predicates(const decl_set & preds);

        void register_plugin(table_plugin * plugin);
        /**
           table_relation_plugins should not be passed to this function since they are
           created automatically when registering a table plugin.
        */
        void register_plugin(relation_plugin * plugin) {
            SASSERT(!plugin->from_table());
            register_relation_plugin_impl(plugin);
        }

        table_plugin & get_appropriate_plugin(const table_signature & t);
        relation_plugin & get_appropriate_plugin(const relation_signature & t);
        table_plugin * try_get_appropriate_plugin(const table_signature & t);
        relation_plugin * try_get_appropriate_plugin(const relation_signature & t);

        table_plugin * get_table_plugin(symbol const& s);
        relation_plugin * get_relation_plugin(symbol const& s);
        relation_plugin & get_relation_plugin(family_id kind);
        void              set_favourite_plugin(relation_plugin* p) { m_favourite_relation_plugin = p; }
        table_relation_plugin & get_table_relation_plugin(table_plugin & tp);
        bool try_get_finite_product_relation_plugin(const relation_plugin & inner, 
            finite_product_relation_plugin * & res);

        table_base * mk_empty_table(const table_signature & s);
        relation_base * mk_implicit_relation(const relation_signature & s, app * expr);

        relation_base * mk_empty_relation(const relation_signature & s, family_id kind);
        relation_base * mk_empty_relation(const relation_signature & s, func_decl* pred);

        relation_base * mk_full_relation(const relation_signature & s, func_decl* pred, family_id kind);
        relation_base * mk_full_relation(const relation_signature & s, func_decl* pred);

        relation_base * mk_table_relation(const relation_signature & s, table_base * table);
        bool mk_empty_table_relation(const relation_signature & s, relation_base * & result);

        bool is_non_explanation(relation_signature const& s) const;


        /**
           \brief Convert relation value to table one.

           This function can be called only for the relation sorts that have a table counterpart.
         */
        void relation_to_table(const relation_sort & sort, const relation_element & from, table_element & to);

        void table_to_relation(const relation_sort & sort, const table_element & from, relation_element & to);
        void table_to_relation(const relation_sort & sort, const table_element & from, 
            const relation_fact::el_proxy & to);
        void table_to_relation(const relation_sort & sort, const table_element & from, 
            relation_element_ref & to);

        bool relation_sort_to_table(const relation_sort & from, table_sort & to);
        void from_predicate(func_decl * pred, unsigned arg_index, relation_sort & result);
        void from_predicate(func_decl * pred, relation_signature & result);

        /**
           \brief Convert relation signature to table signature and return true if successful. If false
           is returned, the value of \c to is undefined.
        */
        bool relation_signature_to_table(const relation_signature & from, table_signature & to);

        void relation_fact_to_table(const relation_signature & s, const relation_fact & from, 
                table_fact & to);
        void table_fact_to_relation(const relation_signature & s, const table_fact & from, 
            relation_fact & to);


        void set_cancel(bool f);


        // -----------------------------------
        //
        // relation operations
        //
        // -----------------------------------

        //TODO: If multiple operation implementations are available, we may want to do something to 
        //select the best one here.

        /**
           If \c allow_product_relation is true, we will create a join that builds a product relation, 
           if there is no other way to do the join. If \c allow_product_relation is false, we will return 
           zero in that case.
        */
        relation_join_fn * mk_join_fn(const relation_base & t1, const relation_base & t2,
            unsigned col_cnt, const unsigned * cols1, const unsigned * cols2, bool allow_product_relation=true);

        relation_join_fn * mk_join_fn(const relation_base & t1, const relation_base & t2,
                const unsigned_vector & cols1, const unsigned_vector & cols2, bool allow_product_relation=true) { 
            SASSERT(cols1.size()==cols2.size());
            return mk_join_fn(t1, t2, cols1.size(), cols1.c_ptr(), cols2.c_ptr(), allow_product_relation);
        }

        /**
            \brief Return functor that transforms a table into one that lacks columns listed in
            \c removed_cols array.

            The \c removed_cols cotains columns of table \c t in strictly ascending order.
            */
        relation_transformer_fn * mk_project_fn(const relation_base & t, unsigned col_cnt, 
            const unsigned * removed_cols);

        relation_transformer_fn * mk_project_fn(const relation_base & t, const unsigned_vector & removed_cols) { 
            return mk_project_fn(t, removed_cols.size(), removed_cols.c_ptr()); 
        }

        /**
            \brief Return an operation that is a composition of a join an a project operation.
        */
        relation_join_fn * mk_join_project_fn(const relation_base & t1, const relation_base & t2,
                unsigned joined_col_cnt, const unsigned * cols1, const unsigned * cols2, 
                unsigned removed_col_cnt, const unsigned * removed_cols, bool allow_product_relation_join=true);

        relation_join_fn * mk_join_project_fn(const relation_base & t1, const relation_base & t2,
                const unsigned_vector & cols1, const unsigned_vector & cols2, 
                const unsigned_vector & removed_cols, bool allow_product_relation_join=true) {
            return mk_join_project_fn(t1, t2, cols1.size(), cols1.c_ptr(), cols2.c_ptr(), removed_cols.size(), 
                removed_cols.c_ptr(), allow_product_relation_join);
        }

        relation_transformer_fn * mk_rename_fn(const relation_base & t, unsigned permutation_cycle_len, 
            const unsigned * permutation_cycle);
        relation_transformer_fn * mk_rename_fn(const relation_base & t, const unsigned_vector & permutation_cycle) { 
            return mk_rename_fn(t, permutation_cycle.size(), permutation_cycle.c_ptr());
        }

        /**
           Like \c mk_rename_fn, only the permutation is not specified by cycle, but by a permutated array
           of column number.
        */
        relation_transformer_fn * mk_permutation_rename_fn(const relation_base & t, 
            const unsigned * permutation);
        relation_transformer_fn * mk_permutation_rename_fn(const relation_base & t, 
                const unsigned_vector permutation) {
            SASSERT(t.get_signature().size()==permutation.size());
            return mk_permutation_rename_fn(t, permutation.c_ptr());
        }


        /**
            The post-condition for an ideal union operation is be

            Union(tgt, src, delta):
                tgt_1==tgt_0 \union src
                delta_1== delta_0 \union ( tgt_1 \setminus tgt_0 )

            A required post-condition is

            Union(tgt, src, delta):
                tgt_1==tgt_0 \union src
                tgt_1==tgt_0 => delta_1==delta_0
                delta_0 \subset delta_1
                delta_1 \subset (delta_0 \union tgt_1)
                ( tgt_1 \setminus tgt_0 ) \subset delta_1

            So that a sufficient implementation is

            Union(tgt, src, delta) {
                oldTgt:=tgt.clone();
                tgt:=tgt \union src
                if(tgt!=oldTgt) {
                    delta:=delta \union src    //also ?delta \union tgt? would work
                }
            }

            If rules are compiled with all_or_nothing_deltas parameter set to true, a sufficient 
            post-condition is
            Union(tgt, src, delta):
                tgt_1==tgt_0 \union src
                (tgt_1==tgt_0 ||  delta_0 is non-empty) <=> delta_1 is non-empty
            */
        relation_union_fn * mk_union_fn(const relation_base & tgt, const relation_base & src, 
            const relation_base * delta);

        relation_union_fn * mk_union_fn(const relation_base & tgt, const relation_base & src) { 
            return mk_union_fn(tgt, src, static_cast<relation_base *>(0));
        }

        /**
            Similar to union, but this one should be used inside loops to allow for abstract 
            domain convergence.
        */
        relation_union_fn * mk_widen_fn(const relation_base & tgt, const relation_base & src, 
            const relation_base * delta); 

        relation_mutator_fn * mk_filter_identical_fn(const relation_base & t, unsigned col_cnt, 
            const unsigned * identical_cols);
        relation_mutator_fn * mk_filter_identical_fn(const relation_base & t, const unsigned_vector identical_cols) {
            return mk_filter_identical_fn(t, identical_cols.size(), identical_cols.c_ptr());
        }

        relation_mutator_fn * mk_filter_equal_fn(const relation_base & t, const relation_element & value, 
            unsigned col);

        relation_mutator_fn * mk_filter_interpreted_fn(const relation_base & t, app * condition);


        relation_transformer_fn * mk_filter_interpreted_and_project_fn(const relation_base & t, app * condition,
            unsigned removed_col_cnt, const unsigned * removed_cols);

        relation_mutator_fn * mk_apply_sequential_fn(unsigned n, relation_mutator_fn* * mutators);


        /**
            \brief Operations that returns all rows of \c t for which is column \c col equal to \c value
            with the column \c col removed.

            This operation can often be efficiently implemented and is useful for evaluating rules 
            of the form

            F(x):-P("c",x).
            */
        relation_transformer_fn * mk_select_equal_and_project_fn(const relation_base & t, 
                const relation_element & value, unsigned col);


        relation_intersection_filter_fn * mk_filter_by_intersection_fn(const relation_base & tgt, 
            const relation_base & src, unsigned joined_col_cnt, 
            const unsigned * tgt_cols, const unsigned * src_cols);
        relation_intersection_filter_fn * mk_filter_by_intersection_fn(const relation_base & tgt, 
                const relation_base & src, const unsigned_vector & tgt_cols, const unsigned_vector & src_cols) { 
            SASSERT(tgt_cols.size()==src_cols.size());
            return mk_filter_by_intersection_fn(tgt, src, tgt_cols.size(), tgt_cols.c_ptr(), src_cols.c_ptr());
        }
        relation_intersection_filter_fn * mk_filter_by_intersection_fn(const relation_base & tgt, 
                const relation_base & src);

        /**
            The filter_by_negation postcondition:
            filter_by_negation(tgt, neg, columns in tgt: c1,...,cN, 
                                            corresponding columns in neg: d1,...,dN):
            tgt_1:={x: x\in tgt_0 && ! \exists y: ( y \in neg & pi_c1(x)= pi_d1(y) & ... & pi_cN(x)= pi_dN(y) ) }
            */
        relation_intersection_filter_fn * mk_filter_by_negation_fn(const relation_base & t, 
            const relation_base & negated_obj, unsigned joined_col_cnt, 
            const unsigned * t_cols, const unsigned * negated_cols);
        relation_intersection_filter_fn * mk_filter_by_negation_fn(const relation_base & t, 
                const relation_base & negated_obj, const unsigned_vector & t_cols, 
                const unsigned_vector & negated_cols) {
            SASSERT(t_cols.size()==negated_cols.size());
            return mk_filter_by_negation_fn(t, negated_obj, t_cols.size(), t_cols.c_ptr(), negated_cols.c_ptr());
        }


        // -----------------------------------
        //
        // table operations
        //
        // -----------------------------------


        table_join_fn * mk_join_fn(const table_base & t1, const table_base & t2,
            unsigned col_cnt, const unsigned * cols1, const unsigned * cols2);

        table_join_fn * mk_join_fn(const table_base & t1, const table_base & t2,
                const unsigned_vector & cols1, const unsigned_vector & cols2) { 
            SASSERT(cols1.size()==cols2.size());
            return mk_join_fn(t1, t2, cols1.size(), cols1.c_ptr(), cols2.c_ptr());
        }

        /**
            \brief Return functor that transforms a table into one that lacks columns listed in
            \c removed_cols array.

            The \c removed_cols cotains columns of table \c t in strictly ascending order.

            If a project operation removes a non-functional column, all functional columns become 
            non-functional (so that none of the values in functional columns are lost)
            */
        table_transformer_fn * mk_project_fn(const table_base & t, unsigned col_cnt, 
            const unsigned * removed_cols);

        table_transformer_fn * mk_project_fn(const table_base & t, const unsigned_vector & removed_cols) { 
            return mk_project_fn(t, removed_cols.size(), removed_cols.c_ptr()); 
        }

        /**
            \brief Return an operation that is a composition of a join an a project operation.

            This operation is equivalent to the two operations performed separately, unless functional 
            columns are involved.
               
            The ordinary project would make all of the functional columns into non-functional if any 
            non-functional column was removed. In function, however, we group columns into equivalence 
            classes (according to the equalities in \c cols1 and \c cols2) and make everything non-functional 
            only if some equivalence class of non-functional columns would have no non-functional columns 
            remain after the removal. 
            
            This behavior is implemented in the \c table_signature::from_join_project function.
        */
        table_join_fn * mk_join_project_fn(const table_base & t1, const table_base & t2,
                unsigned joined_col_cnt, const unsigned * cols1, const unsigned * cols2, 
                unsigned removed_col_cnt, const unsigned * removed_cols);

        table_join_fn * mk_join_project_fn(const table_base & t1, const table_base & t2,
                const unsigned_vector & cols1, const unsigned_vector & cols2, 
                const unsigned_vector & removed_cols) {
            return mk_join_project_fn(t1, t2, cols1.size(), cols1.c_ptr(), cols2.c_ptr(), removed_cols.size(), 
                removed_cols.c_ptr());
        }

        table_transformer_fn * mk_rename_fn(const table_base & t, unsigned permutation_cycle_len, 
            const unsigned * permutation_cycle);
        table_transformer_fn * mk_rename_fn(const table_base & t, const unsigned_vector & permutation_cycle) { 
            return mk_rename_fn(t, permutation_cycle.size(), permutation_cycle.c_ptr());
        }

        /**
           Like \c mk_rename_fn, only the permutation is not specified by cycle, but by a permutated array
           of column number.
        */
        table_transformer_fn * mk_permutation_rename_fn(const table_base & t, const unsigned * permutation);
        table_transformer_fn * mk_permutation_rename_fn(const table_base & t, const unsigned_vector permutation) {
            SASSERT(t.get_signature().size()==permutation.size());
            return mk_permutation_rename_fn(t, permutation.c_ptr());
        }


        /**
            The post-condition for an ideal union operation is be

            Union(tgt, src, delta):
                tgt_1==tgt_0 \union src
                delta_1== delta_0 \union ( tgt_1 \setminus tgt_0 )

            A required post-condition is

            Union(tgt, src, delta):
                tgt_1==tgt_0 \union src
                tgt_1==tgt_0 => delta_1==delta_0
                delta_0 \subset delta_1
                delta_1 \subset (delta_0 \union tgt_1)
                ( tgt_1 \setminus tgt_0 ) \subset delta_1

            So that a sufficient implementation is

            Union(tgt, src, delta) {
                oldTgt:=tgt.clone();
                tgt:=tgt \union src
                if(tgt!=oldTgt) {
                    delta:=delta \union src    //also ?delta \union tgt? would work
                }
            }

            If rules are compiled with all_or_nothing_deltas parameter set to true, a sufficient 
            post-condition is
            Union(tgt, src, delta):
                tgt_1==tgt_0 \union src
                (tgt_1==tgt_0 ||  delta_0 is non-empty) <=> delta_1 is non-empty
            */
        table_union_fn * mk_union_fn(const table_base & tgt, const table_base & src, 
            const table_base * delta);

        table_union_fn * mk_union_fn(const table_base & tgt, const table_base & src) { 
            return mk_union_fn(tgt, src, static_cast<table_base *>(0));
        }

        /**
            Similar to union, but this one should be used inside loops to allow for abstract 
            domain convergence.
        */
        table_union_fn * mk_widen_fn(const table_base & tgt, const table_base & src, 
            const table_base * delta); 

        table_mutator_fn * mk_filter_identical_fn(const table_base & t, unsigned col_cnt, 
            const unsigned * identical_cols);
        table_mutator_fn * mk_filter_identical_fn(const table_base & t, const unsigned_vector identical_cols) {
            return mk_filter_identical_fn(t, identical_cols.size(), identical_cols.c_ptr());
        }

        table_mutator_fn * mk_filter_equal_fn(const table_base & t, const table_element & value, 
            unsigned col);

        table_mutator_fn * mk_filter_interpreted_fn(const table_base & t, app * condition);

        table_transformer_fn * mk_filter_interpreted_and_project_fn(const table_base & t, app * condition,
            unsigned removed_col_cnt, const unsigned * removed_cols);

        /**
            \brief Operations that returns all rows of \c t for which is column \c col equal to \c value
            with the column \c col removed.

            This operation can often be efficiently implemented and is useful for evaluating rules 
            of the form

            F(x):-P("c",x).
            */
        table_transformer_fn * mk_select_equal_and_project_fn(const table_base & t, 
                const table_element & value, unsigned col);

        table_intersection_filter_fn * mk_filter_by_intersection_fn(const table_base & t, 
            const table_base & src, unsigned joined_col_cnt, const unsigned * t_cols, const unsigned * src_cols);
        table_intersection_filter_fn * mk_filter_by_intersection_fn(const table_base & t, 
                const table_base & src, const unsigned_vector & t_cols, const unsigned_vector & src_cols) { 
            SASSERT(t_cols.size()==src_cols.size());
            return mk_filter_by_intersection_fn(t, src, t_cols.size(), t_cols.c_ptr(), src_cols.c_ptr());
        }

        /**
            The filter_by_negation postcondition:
            filter_by_negation(tgt, neg, columns in tgt: c1,...,cN, 
                                            corresponding columns in neg: d1,...,dN):
            tgt_1:={x: x\in tgt_0 && ! \exists y: ( y \in neg & pi_c1(x)= pi_d1(y) & ... & pi_cN(x)= pi_dN(y) ) }
            */
        table_intersection_filter_fn * mk_filter_by_negation_fn(const table_base & t, const table_base & negated_obj, 
            unsigned joined_col_cnt, const unsigned * t_cols, const unsigned * negated_cols);
        table_intersection_filter_fn * mk_filter_by_negation_fn(const table_base & t, const table_base & negated_obj, 
                const unsigned_vector & t_cols, const unsigned_vector & negated_cols) {
            SASSERT(t_cols.size()==negated_cols.size());
            return mk_filter_by_negation_fn(t, negated_obj, t_cols.size(), t_cols.c_ptr(), negated_cols.c_ptr());
        }

        /**
           combined filter by negation with a join.
         */
        table_intersection_join_filter_fn* mk_filter_by_negated_join_fn(
            const table_base & t, 
            const table_base & src1, 
            const table_base & src2, 
            unsigned_vector const& t_cols,
            unsigned_vector const& src_cols,
            unsigned_vector const& src1_cols,
            unsigned_vector const& src2_cols);


        /**
            \c t must contain at least one functional column.

            Created object takes ownership of the \c mapper object.
        */
        virtual table_mutator_fn * mk_map_fn(const table_base & t, table_row_mutator_fn * mapper);

        /**
            \c t must contain at least one functional column.

            Created object takes ownership of the \c mapper object.
        */
        virtual table_transformer_fn * mk_project_with_reduce_fn(const table_base & t, unsigned col_cnt, 
            const unsigned * removed_cols, table_row_pair_reduce_fn * reducer);




        // -----------------------------------
        //
        // output functions
        //
        // -----------------------------------


        std::string to_nice_string(const relation_element & el) const;
        /**
           This one may give a nicer representation of \c el than the 
           \c to_nice_string(const relation_element & el) function, by unsing the information about the sort
           of the element.
        */
        std::string to_nice_string(const relation_sort & s, const relation_element & el) const;
        std::string to_nice_string(const relation_sort & s) const;
        std::string to_nice_string(const relation_signature & s) const;

        void display(std::ostream & out) const;
        void display_relation_sizes(std::ostream & out) const;
        void display_output_tables(rule_set const& rules, std::ostream & out) const;

    private:
        relation_intersection_filter_fn * try_mk_default_filter_by_intersection_fn(const relation_base & t, 
            const relation_base & src, unsigned joined_col_cnt, 
            const unsigned * t_cols, const unsigned * src_cols);

    };

    /**
       This is a helper class for relation_plugins whose relations can be of various kinds.
    */
    template<class Spec, class Hash, class Eq=vector_eq_proc<Spec> >
    class rel_spec_store {
        typedef relation_signature::hash r_hash;
        typedef relation_signature::eq r_eq;

        typedef map<Spec, unsigned, Hash, Eq > family_id_idx_store;
        typedef map<relation_signature, family_id_idx_store *, r_hash, r_eq> sig2store;

        typedef u_map<Spec> family_id2spec;
        typedef map<relation_signature, family_id2spec *, r_hash, r_eq> sig2spec_store;

        relation_plugin &  m_parent;
        svector<family_id> m_allocated_kinds;
        sig2store          m_kind_assignment;
        sig2spec_store     m_kind_specs;


        relation_manager & get_manager() { return m_parent.get_manager(); }

        void add_new_kind() {
            add_available_kind(get_manager().get_next_relation_fid(m_parent));
        }

    public:
        rel_spec_store(relation_plugin & parent) : m_parent(parent) {}

        ~rel_spec_store() {
            reset_dealloc_values(m_kind_assignment);
            reset_dealloc_values(m_kind_specs);
        }

        void add_available_kind(family_id k) {
            m_allocated_kinds.push_back(k);
        }

        bool contains_signature(relation_signature const& sig) const {
            return m_kind_assignment.contains(sig);
        }

        family_id get_relation_kind(const relation_signature & sig, const Spec & spec) {
            typename sig2store::entry * e = m_kind_assignment.find_core(sig);
            if(!e) {
                e = m_kind_assignment.insert_if_not_there2(sig, alloc(family_id_idx_store));
                m_kind_specs.insert(sig, alloc(family_id2spec));
            }
            family_id_idx_store & ids = *e->get_data().m_value;
            
            unsigned res_idx;
            if(!ids.find(spec, res_idx)) {
                res_idx = ids.size();
                if(res_idx==m_allocated_kinds.size()) {
                    add_new_kind();
                }
                SASSERT(res_idx<m_allocated_kinds.size());
                ids.insert(spec, res_idx);

                family_id2spec * idspecs = m_kind_specs.find(sig);
                idspecs->insert(m_allocated_kinds[res_idx], spec);
            }
            return m_allocated_kinds[res_idx];
        }

        void get_relation_spec(const relation_signature & sig, family_id kind, Spec & spec) {
            family_id2spec * idspecs = m_kind_specs.find(sig);
            spec = idspecs->find(kind);
        }

    };

};

#endif /* _DL_RELATION_MANAGER_H_ */

