/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    seq_regex.h

Abstract:

    Solver for regexes 

Author:

    Nikolaj Bjorner (nbjorner) 2020-5-22

--*/
#pragma once

#include "util/scoped_vector.h"
#include "util/state_graph.h"
#include "ast/seq_decl_plugin.h"
#include "ast/rewriter/seq_rewriter.h"
#include "smt/smt_context.h"
#include "smt/seq_skolem.h"

namespace smt {

    class theory_seq;

    class seq_regex {
        // Data about a constraint of the form (str.in_re s R)
        struct s_in_re {
            literal m_lit;
            expr*   m_s;
            expr*   m_re;
            bool    m_active;
        s_in_re(literal l, expr* s, expr* r):
            m_lit(l), m_s(s), m_re(r), m_active(true) {}
        };

        theory_seq&                      th;
        context&                         ctx;
        ast_manager&                     m;
        vector<s_in_re>                  m_s_in_re;

        /*
            state_graph for dead state detection, and associated methods
        */
        state_graph                    m_state_graph;
        ptr_addr_map<expr, unsigned>   m_expr_to_state;
        expr_ref_vector                m_state_to_expr;
        unsigned                       m_max_state_graph_size { 10000 };
        // Convert between expressions and states (IDs)
        unsigned get_state_id(expr* e);
        expr* get_expr_from_id(unsigned id);
        // Cycle-detection heuristic
        // Note: Doesn't need to be sound or complete (doesn't affect soundness)
        unsigned concat_length(expr* r);
        unsigned re_rank(expr* r);
        bool can_be_in_cycle(expr* r1, expr* r2);
        // Update the graph
        bool update_state_graph(expr* r);

        // Printing expressions for seq_regex_brief
        std::string state_str(expr* e);
        std::string expr_id_str(expr* e);

        /*
            Solvers and utilities
        */
        seq_util& u();
        class seq_util::re& re();
        class seq_util::str& str();
        seq_rewriter& seq_rw();
        seq_skolem& sk();
        arith_util& a();

        bool is_string_equality(literal lit);

        void rewrite(expr_ref& e);

        bool coallesce_in_re(literal lit);

        bool block_unfolding(literal lit, unsigned i);

        expr_ref mk_first(expr* r, expr* n);

        bool is_member(expr* r, expr* u);

        expr_ref symmetric_diff(expr* r1, expr* r2);

        expr_ref is_nullable_wrapper(expr* r);
        expr_ref derivative_wrapper(expr* hd, expr* r);

        void get_cofactors(expr* r, expr_ref_vector& conds, expr_ref_pair_vector& result);
        void get_cofactors(expr* r, expr_ref_pair_vector& result) {
            expr_ref_vector conds(m);
            get_cofactors(r, conds, result);
        }
        void get_all_derivatives(expr* r, expr_ref_vector& results);

    public:

        seq_regex(theory_seq& th);

        void push_scope() {}
        void pop_scope(unsigned num_scopes) {}
        bool can_propagate() const { return false; }
        bool propagate() const { return false; }

        void propagate_in_re(literal lit);

        // (accept s i r) means 
        // the suffix of s after the first i characters is a member of r
        void propagate_accept(literal lit);

        void propagate_eq(expr* r1, expr* r2);

        void propagate_ne(expr* r1, expr* r2);
        
        void propagate_is_non_empty(literal lit);

        void propagate_is_empty(literal lit);
        
    };

};
