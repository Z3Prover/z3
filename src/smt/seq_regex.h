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
#include "ast/rewriter/seq_skolem.h"
#include "smt/smt_context.h"

/*
    *** Tracing and debugging in this module and related modules ***

    Tracing and debugging for the regex solver are split across several
    command-line flags.

        TRACING

        -tr:seq_regex and -tr:seq_regex_brief
        These are the main tags to trace what the regex solver is doing.
        They mostly trace the same things, except that seq_regex_brief
        avoids printing out expressions and tries to abbreviate the output
        as much as possible. seq_regex_brief shows the following output:
            Top-level propagations:
                PIR:      Propagating an in_re constraint
                PE/PNE:   Propagating an empty/non-empty constraint
                PEQ/PNEQ: Propagating a not-equal constraint
                PA:       Propagating an accept constraint
            In tracing, arguments are generally put in parentheses.
            To achieve abbreviated output, expressions are traced in one of two
            ways:
                id243 (expr ID):  the regex or expression with id 243
                3     (state ID): the regex with state ID 3
            When a regex is newly assigned to a state ID, we print this:
                new(id606)=4
            Of these, PA is the most important, and traces as follows:
                PA(x@i,r): propagate accept for string x at index i, regex r.
                (empty), (dead), (blocked), (unfold): info about whether this
                    PA was cut off early, or unfolded into the derivatives
                    (next states)
                d(r1)=r2: r2 is the derivative of r1
                n(r1)=b:  b = whether r1 is nullable or not
                USG(r):   updating state graph for regex r (add all derivatives)

        -tr:state_graph
        This is the tracing done by util/state_graph, the data structure
        that seq_regex uses to track live and dead regexes, which can
        altneratively be used to get a high-level picture of what states
        are being explored and updated as the solver progresses.

        -tr:seq_regex_verbose
        Used for some more frequent tracing (in the style of seq_regex,
        not in the style of seq_regex_brief)

        -tr:seq and -tr:seq_verbose
        These are the underlying sequence theory tracing, often used by
        the rewriter.

        DEBUGGING AND VIEWING STATE GRAPH GRAPHICAL OUTPUT

        -dbg:seq_regex
        Debugging that checks invariants. Currently, checks that derivative
        normal form is correctly preserved in the rewriter.

        -dbg:state_graph
        Debugging for the state graph, which
        1. Checks state graph invariants, and
        2. Generates the files .z3-state-graph.dgml and .z3-state-graph.dot
           which can be used to visually view the state graph being explored,
           during or after executing Z3.
           The output can be viewed:
              - Using Visual Studio for .dgml
              - Using a tool such as xdot (`xdot .z3-state-graph.dot`) for .dot
*/

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
        ptr_addr_map<expr, unsigned>   m_expr_to_state;
        expr_ref_vector                m_state_to_expr;
        state_graph                    m_state_graph;
        /* map from uninterpreted regex constants to assigned regex expressions by EQ */
        // expr_map                       m_const_to_expr;
        unsigned                       m_max_state_graph_size { 10000 };
        // Convert between expressions and states (IDs)
        unsigned get_state_id(expr* e);
        expr* get_expr_from_id(unsigned id);
        // Cycle-detection heuristic
        // Note: Doesn't need to be sound or complete (doesn't affect soundness)
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
        class seq_util::rex& re();
        class seq_util::str& str();
        seq_rewriter& seq_rw();
        seq::skolem& sk();
        arith_util& a();

        bool is_string_equality(literal lit);

        // Get a regex which overapproximates a given string
        expr_ref get_overapprox_regex(expr* s);

        void rewrite(expr_ref& e);

        bool coallesce_in_re(literal lit);

        bool block_unfolding(literal lit, unsigned i);

        expr_ref mk_first(expr* r, expr* n);

        bool is_member(expr* r, expr* u);

        expr_ref symmetric_diff(expr* r1, expr* r2);

        expr_ref is_nullable_wrapper(expr* r);
        expr_ref derivative_wrapper(expr* hd, expr* r);

        // Various support for unfolding derivative expressions that are
        // returned by derivative_wrapper
        expr_ref mk_deriv_accept(expr* s, unsigned i, expr* r);
        void get_all_derivatives(expr* r, expr_ref_vector& results);
        void get_cofactors(expr* r, expr_ref_pair_vector& result);
        void get_cofactors_rec(expr* r, expr_ref_vector& conds,
                               expr_ref_pair_vector& result);

        /* 
           Pretty print the regex of the state id to the out stream, 
           seq_regex_ptr must be a pointer to seq_regex and the 
           id must be a valid state id or else nothing is printed. 
        */
        static void pp_state(void* seq_regex_ptr, std::ostream& out, unsigned id, bool html_encode) {
            seq_regex* sr = (seq_regex*)seq_regex_ptr;
            if (sr) {
                seq_util::rex re_util(sr->re());
                if (1 <= id && id <= sr->m_state_to_expr.size()) {
                    expr* r = sr->get_expr_from_id(id);
                    seq_util::rex::pp(re_util, r, html_encode).display(out);
                }
            }
        }

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
