/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    pdr_manager.h

Abstract:

    A manager class for PDR, taking care of creating of AST 
    objects and conversions between them.

Author:

    Krystof Hoder (t-khoder) 2011-8-25.

Revision History:

--*/

#ifndef PDR_MANAGER_H_
#define PDR_MANAGER_H_

#include <utility>
#include <map>
#include "ast/rewriter/bool_rewriter.h"
#include "ast/rewriter/expr_replacer.h"
#include "ast/expr_substitution.h"
#include "util/map.h"
#include "util/ref_vector.h"
#include "smt/smt_kernel.h"
#include "muz/pdr/pdr_util.h"
#include "muz/pdr/pdr_sym_mux.h"
#include "muz/pdr/pdr_farkas_learner.h"
#include "muz/pdr/pdr_smt_context_manager.h"
#include "muz/base/dl_rule.h"


namespace smt {
    class context;
}

namespace pdr {

    struct relation_info {
        func_decl_ref         m_pred;
        func_decl_ref_vector  m_vars;
        expr_ref              m_body;
        relation_info(ast_manager& m, func_decl* pred, ptr_vector<func_decl> const& vars, expr* b): 
            m_pred(pred, m), m_vars(m, vars.size(), vars.c_ptr()), m_body(b, m) {}
        relation_info(relation_info const& other): m_pred(other.m_pred), m_vars(other.m_vars), m_body(other.m_body) {}
    };

    class unknown_exception {};

    class inductive_property {
        ast_manager&             m;
        model_converter_ref      m_mc;
        vector<relation_info>    m_relation_info;
        expr_ref fixup_clauses(expr* property) const;
        expr_ref fixup_clause(expr* clause) const;
    public:
        inductive_property(ast_manager& m, model_converter_ref& mc, vector<relation_info> const& relations):
            m(m),
            m_mc(mc),
            m_relation_info(relations) {}

        std::string to_string() const;

        expr_ref to_expr() const;

        void to_model(model_ref& md) const;
        
        void display(datalog::rule_manager& rm, ptr_vector<datalog::rule> const& rules, std::ostream& out) const;
    };

    class manager
    {
        ast_manager&      m;
        smt_params& m_fparams;
        
        mutable bool_rewriter m_brwr;
               
        sym_mux               m_mux;
        expr_ref              m_background;
        decl_vector           m_o0_preds;
        pdr::smt_context_manager   m_contexts;
        
        /** whenever we need an unique number, we get this one and increase */
        unsigned m_next_unique_num;
        
               
        unsigned n_index() const { return 0; }
        unsigned o_index(unsigned i) const { return i+1; }
        
        void add_new_state(func_decl * s);
        
    public:
        manager(smt_params& fparams, unsigned max_num_contexts, ast_manager & manager);
        
        ast_manager& get_manager() const { return m; }
        smt_params& get_fparams() const { return m_fparams; }
        bool_rewriter& get_brwr() const { return m_brwr; }

        expr_ref mk_and(unsigned sz, expr* const* exprs);
        expr_ref mk_and(expr_ref_vector const& exprs) {
            return mk_and(exprs.size(), exprs.c_ptr());
        }
        expr_ref mk_and(expr* a, expr* b) {
            expr* args[2] = { a, b };
            return mk_and(2, args);
        }
        expr_ref mk_or(unsigned sz, expr* const* exprs);
        expr_ref mk_or(expr_ref_vector const& exprs) {
            return mk_or(exprs.size(), exprs.c_ptr());
        }

        expr_ref mk_not_and(expr_ref_vector const& exprs);
        
        void get_or(expr* e, expr_ref_vector& result);
        
        //"o" predicates stand for the old states and "n" for the new states
        func_decl * get_o_pred(func_decl * s, unsigned idx);
        func_decl * get_n_pred(func_decl * s);
        
        /**
           Marks symbol as non-model which means it will not appear in models collected by 
           get_state_cube_from_model function.
           This is to take care of auxiliary symbols introduced by the disjunction relations
           to relativize lemmas coming from disjuncts.
        */
        void mark_as_non_model(func_decl * p) {
            m_mux.mark_as_non_model(p);
        }
        
        
        func_decl * const * begin_o0_preds() const { return m_o0_preds.begin(); }
        func_decl * const * end_o0_preds() const { return m_o0_preds.end(); }
        
        bool is_state_pred(func_decl * p) const { return m_mux.is_muxed(p); }
        func_decl * to_o0(func_decl * p) { return m_mux.conv(m_mux.get_primary(p), 0, o_index(0)); }
        
        bool is_o(func_decl * p, unsigned idx) const { 
            return m_mux.has_index(p, o_index(idx)); 
        }
        bool is_o(expr* e, unsigned idx) const {
            return is_app(e) && is_o(to_app(e)->get_decl(), idx);
        }
        bool is_o(func_decl * p) const { 
            unsigned idx;
            return m_mux.try_get_index(p, idx) && idx!=n_index();
        }
        bool is_o(expr* e) const {
            return is_app(e) && is_o(to_app(e)->get_decl());
        }
        bool is_n(func_decl * p) const { 
            return m_mux.has_index(p, n_index()); 
        }
        bool is_n(expr* e) const {
            return is_app(e) && is_n(to_app(e)->get_decl());
        }
        
        /** true if p should not appead in models propagates into child relations */
        bool is_non_model_sym(func_decl * p) const 
        { return m_mux.is_non_model_sym(p); }
        
        
        /** true if f doesn't contain any n predicates */
        bool is_o_formula(expr * f) const { 
            return !m_mux.contains(f, n_index()); 
        }

        /** true if f contains only o state preds of index o_idx */
        bool is_o_formula(expr * f, unsigned o_idx) const { 
            return m_mux.is_homogenous_formula(f, o_index(o_idx)); 
        }
        /** true if f doesn't contain any o predicates */
        bool is_n_formula(expr * f) const { 
            return m_mux.is_homogenous_formula(f, n_index()); 
        }
        
        func_decl * o2n(func_decl * p, unsigned o_idx) {
            return m_mux.conv(p, o_index(o_idx), n_index()); 
        }
        func_decl * o2o(func_decl * p, unsigned src_idx, unsigned tgt_idx) { 
            return m_mux.conv(p, o_index(src_idx), o_index(tgt_idx)); 
        }
        func_decl * n2o(func_decl * p, unsigned o_idx) {
            return m_mux.conv(p, n_index(), o_index(o_idx)); 
        }
    
        void formula_o2n(expr * f, expr_ref & result, unsigned o_idx, bool homogenous=true) 
        { m_mux.conv_formula(f, o_index(o_idx), n_index(), result, homogenous); }
        
        void formula_n2o(expr * f, expr_ref & result, unsigned o_idx, bool homogenous=true) 
        { m_mux.conv_formula(f, n_index(), o_index(o_idx), result, homogenous); }
        
        void formula_n2o(unsigned o_idx, bool homogenous, expr_ref & result) 
        { m_mux.conv_formula(result.get(), n_index(), o_index(o_idx), result, homogenous); }
        
        void formula_o2o(expr * src, expr_ref & tgt, unsigned src_idx, unsigned tgt_idx, bool homogenous=true) 
        { m_mux.conv_formula(src, o_index(src_idx), o_index(tgt_idx), tgt, homogenous); }
        
        /**
           Return true if all state symbols which e contains are of one kind (either "n" or one of "o").
        */
        bool is_homogenous_formula(expr * e) const {
            return m_mux.is_homogenous_formula(e);
        }

        /**
            Collect indices used in expression.
        */
        void collect_indices(expr* e, unsigned_vector& indices) const {
            m_mux.collect_indices(e, indices);
        }

        /**
            Collect used variables of each index.
        */
        void collect_variables(expr* e, vector<ptr_vector<app> >& vars) const {
            m_mux.collect_variables(e, vars);
        }
        
        /**
           Return true iff both s1 and s2 are either "n" or "o" of the same index.
           If one (or both) of them are not state symbol, return false.
        */
        bool have_different_state_kinds(func_decl * s1, func_decl * s2) const {
            unsigned i1, i2;
            return m_mux.try_get_index(s1, i1) && m_mux.try_get_index(s2, i2) && i1!=i2;
        }
        
        /**
           Increase indexes of state symbols in formula by dist.
           The 'N' index becomes 'O' index with number dist-1.
        */
        void formula_shift(expr * src, expr_ref & tgt, unsigned dist) {
            SASSERT(n_index()==0);
            SASSERT(o_index(0)==1);
            m_mux.shift_formula(src, dist, tgt);
        }
        
        void mk_model_into_cube(const expr_ref_vector & mdl, expr_ref & res);
        void mk_core_into_cube(const expr_ref_vector & core, expr_ref & res);
        void mk_cube_into_lemma(expr * cube, expr_ref & res);
        void mk_lemma_into_cube(expr * lemma, expr_ref & res);
        
        /**
           Remove from vec all atoms that do not have an "o" state.
           The order of elements in vec may change.
           An assumption is that atoms having "o" state of given index
           do not have "o" states of other indexes or "n" states.
        */
        void filter_o_atoms(expr_ref_vector& vec, unsigned o_idx) const 
        { m_mux.filter_idx(vec, o_index(o_idx)); }
        void filter_n_atoms(expr_ref_vector& vec) const 
        { m_mux.filter_idx(vec, n_index()); }
        
        /**
           Partition literals into o_lits and others.
        */
        void partition_o_atoms(expr_ref_vector const& lits, 
                               expr_ref_vector& o_lits,
                               expr_ref_vector& other,
                               unsigned o_idx) const {
            m_mux.partition_o_idx(lits, o_lits, other, o_index(o_idx));
        }
        
        void filter_out_non_model_atoms(expr_ref_vector& vec) const
        { m_mux.filter_non_model_lits(vec); }
        
        bool try_get_state_and_value_from_atom(expr * atom, app *& state, app_ref& value);
        bool try_get_state_decl_from_atom(expr * atom, func_decl *& state);
        
        
        std::string pp_model(const model_core & mdl) const
            {  return m_mux.pp_model(mdl); }
        

        void set_background(expr* b) { m_background = b; }
        
        expr* get_background() const { return m_background; }
        
        
        /**
           Return true if we can show that lhs => rhs. The function can have false negatives
           (i.e. when smt::context returns unknown), but no false positives.
           
           bg is background knowledge and can be null
        */
        bool implication_surely_holds(expr * lhs, expr * rhs, expr * bg=nullptr);
        
        unsigned get_unique_num() { return m_next_unique_num++; }
        
        pdr::smt_context* mk_fresh() {  return m_contexts.mk_fresh();   }
        
        void collect_statistics(statistics& st) const { m_contexts.collect_statistics(st); }

        void reset_statistics() { m_contexts.reset_statistics(); }
    };
}

#endif
