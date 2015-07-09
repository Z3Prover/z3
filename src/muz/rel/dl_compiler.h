/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    dl_compiler.h

Abstract:

    <abstract>

Author:

    Krystof Hoder (t-khoder) 2010-09-14.

Revision History:

--*/
#ifndef DL_COMPILER_H_
#define DL_COMPILER_H_

#include<iostream>
#include<list>
#include<utility>

#include "ast.h"
#include "hashtable.h"
#include "map.h"
#include "obj_pair_hashtable.h"
#include "ref_vector.h"
#include "vector.h"

#include "dl_base.h"
#include "dl_context.h"
#include "dl_instruction.h"

namespace datalog {

    class compiler {
        typedef instruction::reg_idx reg_idx;
        typedef hashtable<unsigned, u_hash, u_eq> int_set;
        typedef u_map<unsigned> int2int;
        typedef u_map<unsigned_vector> int2ints;
        typedef obj_map<func_decl, reg_idx> pred2idx;
        typedef unsigned_vector var_vector;
        typedef ptr_vector<func_decl> func_decl_vector;

        enum assembling_column_kind {
            ACK_BOUND_VAR,
            ACK_UNBOUND_VAR,
            ACK_CONSTANT
        };

        /**
            \brief instruction for assembling head relation from a joint relation built
            from rule evaluation.

            ACK_BOUND_VAR(source_column) - encodes that the column contains a variable
                                        bound in the body.

            ACK_UNBOUND_VAR(var_index) - encodes that the column contains a variable that
                                         is unbound (by the corresponding rule body),
                                         var_index is the de-Brujin index (var->get_idx())
                                         of the variable associated with the column.

            ACK_CONSTANT(constant) - encodes that the column contains the constant.

            Examples:

            P(x) :- Q(x,y), Q(y,z)
            The variables in the body relation are [x, y, y, z] indexed as 0, 1, 2, 3.
            The variable x gets the instruction ACK_BOUND_VAR(0)

            P(u,x) :- Q(x,y), Q(y,z)
            The variable u gets the instruction ACK_UNBOUND_VAR(#0)

            P(1, x) :-  Q(x,y), Q(y,z)
            The instruction for column 0 is ACK_CONSTANT(1)

        */
        struct assembling_column_info {
            
            relation_sort domain;           // domain of the column
            assembling_column_kind kind;    // "instruction" tag
            union {
                unsigned source_column;         // for ACK_BOUND_VAR
                unsigned var_index;             // for ACK_UNBOUND_VAR
                relation_element constant;      // for ACK_CONSTANT
            };
        };

        class instruction_observer : public instruction_block::instruction_observer {
            compiler & m_parent;
            rule * m_current;
        public:
            instruction_observer(compiler & parent) : m_parent(parent), m_current(0) {}

            void start_rule(rule * r) { SASSERT(!m_current); m_current=r; }
            void finish_rule() { m_current = 0; }
            virtual void notify(instruction * i) {
                if(m_current) {
                    i->set_accounting_parent_object(m_parent.m_context, m_current);
                }
            }
        };


        context & m_context;
        rule_set const & m_rule_set;
        /**
           Invariant: the \c m_top_level_code never contains the loop that is being constructed,
           so instruction that need to be executed before the loop can be pushed into it.
         */
        instruction_block & m_top_level_code;
        pred2idx m_pred_regs;
        vector<relation_signature>        m_reg_signatures;
        obj_pair_map<sort, app, reg_idx>  m_constant_registers;
        obj_pair_map<sort, decl, reg_idx> m_total_registers;
        obj_map<decl, reg_idx>            m_empty_tables_registers;
        instruction_observer              m_instruction_observer;
        expr_free_vars                    m_free_vars;

        /**
        \brief Finds all the min aggregation functions in the premise of a given rule.
        */
        static void find_min_aggregates(const rule * r, ptr_vector<func_decl>& min_aggregates);

        /**
        \brief Decides whether a predicate is subject to a min aggregation function.

        If \c decl is subject to a min aggregation function, the output parameters are written
        with the neccessary information.

        \returns true if the output paramaters have been written
        */
        static bool prepare_min_aggregate(const func_decl * decl, const ptr_vector<func_decl>& min_aggregates,
            unsigned_vector & group_by_cols, unsigned & min_col);

        /**
           If true, the union operation on the underlying structure only provides the information
           whether the updated relation has changed or not. In this case we do not get anything
           from using delta relations at position of input relations in the saturation loop, so we
           would not do it.
        */
        bool all_or_nothing_deltas() const { return m_context.all_or_nothing_deltas(); }

        /**
           If true, we compile the saturation loops in a way that allows us to use widening.
        */
        bool compile_with_widening() const { return m_context.compile_with_widening(); }

        reg_idx get_fresh_register(const relation_signature & sig);
        reg_idx get_register(const relation_signature & sig, bool reuse, reg_idx r);
        reg_idx get_single_column_register(const relation_sort s);

        /**
           \brief Allocate registers for predicates in \c pred and add them into the \c regs map.

           \c regs must not already contain any predicate from \c preds.
        */
        void get_fresh_registers(const func_decl_set & preds,  pred2idx & regs);

        void make_join(reg_idx t1, reg_idx t2, const variable_intersection & vars, reg_idx & result, 
            bool reuse_t1, instruction_block & acc);
        void make_min(reg_idx source, reg_idx & target, const unsigned_vector & group_by_cols,
            const unsigned min_col, instruction_block & acc);
        void make_join_project(reg_idx t1, reg_idx t2, const variable_intersection & vars, 
            const unsigned_vector & removed_cols, reg_idx & result, bool reuse_t1, instruction_block & acc);
        void make_filter_interpreted_and_project(reg_idx src, app_ref & cond,
            const unsigned_vector & removed_cols, reg_idx & result, bool reuse, instruction_block & acc);
        void make_select_equal_and_project(reg_idx src, const relation_element val, unsigned col,
            reg_idx & result, bool reuse, instruction_block & acc);
        /**
           \brief Create add an union or widen operation and put it into \c acc.
        */
        void make_union(reg_idx src, reg_idx tgt, reg_idx delta, bool widening, instruction_block & acc);
        void make_projection(reg_idx src, unsigned col_cnt, const unsigned * removed_cols, 
            reg_idx & result, bool reuse, instruction_block & acc);
        void make_rename(reg_idx src, unsigned cycle_len, const unsigned * permutation_cycle, 
            reg_idx & result, bool reuse, instruction_block & acc);
        void make_clone(reg_idx src, reg_idx & result, instruction_block & acc);

        /**
           \brief Into \c acc add code that will assemble columns of a relation according to description
           in \c acis0. The source for bound variables is the table in register \c src.

           If \c src is \c execution_context::void_register, it is assumed to be a full relation
           with empty signature.
        */
        void make_assembling_code(rule* compiled_rule, func_decl* head_pred, reg_idx src, const svector<assembling_column_info> & acis0,
            reg_idx & result, bool & dealloc, instruction_block & acc);

        void make_dealloc_non_void(reg_idx r, instruction_block & acc);

        void make_add_constant_column(func_decl* pred, reg_idx src, const relation_sort s, const relation_element val,
            reg_idx & result, bool & dealloc, instruction_block & acc);

        void make_add_unbound_column(rule* compiled_rule, unsigned col_idx, func_decl* pred, reg_idx src, const relation_sort s, reg_idx & result,
            bool & dealloc, instruction_block & acc);
        void make_full_relation(func_decl* pred, const relation_signature & sig, reg_idx & result, 
            instruction_block & acc);

        void add_unbound_columns_for_negation(rule* compiled_rule, func_decl* pred, reg_idx& single_res, expr_ref_vector& single_res_expr,
                                              bool & dealloc, instruction_block& acc);
        
        void make_duplicate_column(reg_idx src, unsigned col, reg_idx & result, bool reuse, instruction_block & acc);
        
        void ensure_predicate_loaded(func_decl * pred, instruction_block & acc);

        /**
           \brief For rule \c r with two positive uninterpreted predicates put into \c res indexes of 
           local variables in a table that results from join of the two positive predicates.

           Used to get input for the "project" part of join-project.
         */
        void get_local_indexes_for_projection(rule * r, unsigned_vector & res);
        void get_local_indexes_for_projection(app * t, var_counter & globals, unsigned ofs, 
            unsigned_vector & res);

        /**
           \brief Into \c acc add instructions that will add new facts following from the rule into 
           \c head_reg, and add the facts that were not in \c head_reg before into \c delta_reg.
        */
        void compile_rule_evaluation_run(rule * r, reg_idx head_reg, const reg_idx * tail_regs, 
            reg_idx delta_reg, bool use_widening, instruction_block & acc);

        void compile_rule_evaluation(rule * r, const pred2idx * input_deltas, reg_idx output_delta, 
            bool use_widening, instruction_block & acc);

        /**
           \brief Generate code to evaluate rules corresponding to predicates in \c head_preds.
           The rules are evaluated in the order their heads appear in the \c head_preds vector.
         */
        void compile_preds(const func_decl_vector & head_preds, const func_decl_set & widened_preds,
            const pred2idx * input_deltas, const pred2idx & output_deltas, instruction_block & acc);

        /**
           \brief Generate code to evaluate predicates in a stratum based on their non-recursive rules.
         */
        void compile_preds_init(const func_decl_vector & head_preds, const func_decl_set & widened_preds,
            const pred2idx * input_deltas, const pred2idx & output_deltas, instruction_block & acc);

        void make_inloop_delta_transition(const pred2idx & global_head_deltas, 
            const pred2idx & global_tail_deltas, const pred2idx & local_deltas, instruction_block & acc);
        void compile_loop(const func_decl_vector & head_preds, const func_decl_set & widened_preds,
            const pred2idx & global_head_deltas, const pred2idx & global_tail_deltas, 
            const pred2idx & local_deltas, instruction_block & acc);
        void compile_dependent_rules(const func_decl_set & head_preds,
            const pred2idx * input_deltas, const pred2idx & output_deltas, 
            bool add_saturation_marks, instruction_block & acc);

        void detect_chains(const func_decl_set & preds, func_decl_vector & ordered_preds, 
            func_decl_set & global_deltas);
        /**
           Return true if there is no dependency inside the \c rules stratum.

           The head predicates in stratum must be strongly connected by dependency.
        */
        bool is_nonrecursive_stratum(const func_decl_set & preds) const;
        /**
        input_deltas==0 --> we use the actual content of relations instead of deltas
        */
        void compile_nonrecursive_stratum(const func_decl_set & preds, 
            const pred2idx * input_deltas, const pred2idx & output_deltas, 
            bool add_saturation_marks, instruction_block & acc);

        void compile_strats(const rule_stratifier & stratifier, 
            const pred2idx * input_deltas, const pred2idx & output_deltas, 
            bool add_saturation_marks, instruction_block & acc);

        bool all_saturated(const func_decl_set & preds) const;

        void reset();

        explicit compiler(context & ctx, rule_set const & rules, instruction_block & top_level_code) 
            : m_context(ctx), 
            m_rule_set(rules),
            m_top_level_code(top_level_code),
            m_instruction_observer(*this) {}
        
        /**
           \brief Compile \c rules in to pseudocode.

           Instructions to load data and perform computations put into \c execution_code
        */
        void do_compilation(instruction_block & execution_code, 
            instruction_block & termination_code);

    public:

        static void compile(context & ctx, rule_set const & rules, instruction_block & execution_code, 
                instruction_block & termination_code) {
            compiler(ctx, rules, execution_code)
                .do_compilation(execution_code, termination_code);
        }

    };


};

#endif /* DL_COMPILER_H_ */

