/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    theory_nseq.h

Abstract:

    Theory solver for strings based on Nielsen transformations
    and lazy regex membership (ZIPT algorithm).

Author:

    Clemens Eisenhofer
    Nikolaj Bjorner (nbjorner) 2025-2-28

--*/
#pragma once

#include "ast/seq_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/rewriter/seq_skolem.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/rewriter/nseq_nielsen.h"
#include "model/seq_factory.h"
#include "smt/smt_theory.h"
#include "smt/smt_arith_value.h"
#include "smt/smt_model_generator.h"
#include "smt/nseq_state.h"

namespace smt {

    class theory_nseq : public theory {
        seq_util         m_util;
        arith_util       m_autil;
        seq_rewriter     m_seq_rewrite;
        th_rewriter      m_rewrite;
        seq::skolem      m_sk;
        arith_value      m_arith_value;
        nseq_state       m_state;
        seq::nielsen     m_nielsen;
        nseq_union_find  m_find;
        bool             m_has_seq;
        bool             m_new_propagation;
        expr_ref_vector  m_fresh_values;  // keep model fresh values alive

        // Theory interface
        final_check_status final_check_eh(unsigned) override;
        bool internalize_atom(app* atom, bool) override;
        bool internalize_term(app*) override;
        void internalize_eq_eh(app* atom, bool_var v) override;
        void new_eq_eh(theory_var, theory_var) override;
        void new_diseq_eh(theory_var, theory_var) override;
        void assign_eh(bool_var v, bool is_true) override;
        bool can_propagate() override;
        void propagate() override;
        void push_scope_eh() override;
        void pop_scope_eh(unsigned num_scopes) override;
        void restart_eh() override;
        void relevant_eh(app* n) override;
        theory* mk_fresh(context* new_ctx) override { return alloc(theory_nseq, *new_ctx); }
        char const* get_name() const override { return "nseq"; }
        void display(std::ostream& out) const override;
        void collect_statistics(::statistics& st) const override;
        model_value_proc* mk_value(enode* n, model_generator& mg) override;
        void init_model(model_generator& mg) override;
        void finalize_model(model_generator& mg) override;
        theory_var mk_var(enode* n) override;
        void apply_sort_cnstr(enode* n, sort* s) override;

        // Axiom management
        void enque_axiom(expr* e);
        void deque_axiom(expr* e);
        void add_axiom(literal l1, literal l2 = null_literal, literal l3 = null_literal,
                        literal l4 = null_literal, literal l5 = null_literal);

        // Propagation helpers
        bool propagate_eq(nseq_dependency* dep, enode* n1, enode* n2);
        bool propagate_eq(nseq_dependency* dep, expr* e1, expr* e2, bool add_to_eqs = true);
        bool propagate_lit(nseq_dependency* dep, literal lit);
        void set_conflict(nseq_dependency* dep, literal_vector const& lits = literal_vector());

        // Helpers
        void add_length(expr* l);
        void ensure_length_axiom(expr* e);
        literal mk_literal(expr* e);
        literal mk_eq_empty(expr* e, bool phase = true);
        expr_ref mk_len(expr* s);
        expr_ref mk_concat(expr_ref_vector const& es, sort* s);

        // Nielsen equation solving
        bool solve_eqs();
        bool solve_eq(nseq_eq const& eq);
        bool branch_eq(expr_ref_vector const& lhs, expr_ref_vector const& rhs, nseq_dependency* dep);
        bool branch_eq_prefix(expr_ref_vector const& lhs, expr_ref_vector const& rhs, nseq_dependency* dep);
        bool branch_var_prefix(expr* x, expr_ref_vector const& other, nseq_dependency* dep);
        bool split_variable(expr_ref_vector const& lhs, expr_ref_vector const& rhs, nseq_dependency* dep);
        bool propagate_ground_split(expr_ref_vector const& lhs, expr_ref_vector const& rhs, nseq_dependency* dep);
        bool canonize(expr_ref_vector const& src, expr_ref_vector& dst, nseq_dependency*& dep);
        bool all_eqs_solved();
        bool check_length_conflict(expr* x, expr_ref_vector const& es, nseq_dependency* dep);

        // Predicate handling (prefix, suffix, contains)
        bool reduce_predicates();
        bool reduce_pred(nseq_pred const& pred);
        bool reduce_prefix(expr* s, expr* t, bool sign, nseq_dependency* dep);
        bool reduce_suffix(expr* s, expr* t, bool sign, nseq_dependency* dep);
        bool reduce_contains(expr* haystack, expr* needle, bool sign, nseq_dependency* dep);

        // Disequality checking
        bool check_disequalities();
        bool check_diseq(nseq_ne const& ne);

        // Regex membership
        bool check_regex_memberships();
        bool check_regex_mem(nseq_mem const& mem);
        bool add_regex_length_axioms(nseq_mem const& mem);
        bool synthesize_regex_string(expr* regex, unsigned len, zstring& result);
        bool dfs_regex(expr* r, unsigned target_len, unsigned cur_len, zstring& result);
        bool is_ground_string(expr* e, zstring& s);
        expr_ref derive_regex(expr* regex, zstring const& prefix);
        bool all_mems_checked();
        expr* find_regex_for(expr* e);
        expr* find_substr_regex(expr* base, unsigned pos, unsigned total_len, unsigned& cover_len);

        // String operation reductions
        void reduce_op(expr* e);
        void reduce_replace(expr* e);
        void reduce_at(expr* e);
        void reduce_extract(expr* e);
        void reduce_index(expr* e);
        void reduce_itos(expr* e);
        void reduce_stoi(expr* e);

        // Length reasoning
        void add_length_axiom(expr* n);
        expr_ref build_length_sum(expr_ref_vector const& es);
        bool check_zero_length();
        bool propagate_length_eqs();
        bool get_length(expr* e, rational& val);
        bool lower_bound(expr* e, rational& lo);
        bool upper_bound(expr* e, rational& hi);

        // Model construction
        bool eval_string(expr* e, zstring& result);
        bool eval_string_in_eclass(expr* e, zstring& result);

    public:
        theory_nseq(context& ctx);
        ~theory_nseq() override;
        void init() override;

        // union_find callbacks
        trail_stack& get_trail_stack() { return m_state.trail(); }
        void merge_eh(theory_var, theory_var, theory_var, theory_var) {}
        void after_merge_eh(theory_var, theory_var, theory_var, theory_var) {}
        void unmerge_eh(theory_var, theory_var) {}
    };
}

