/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    seq_regex.h

Abstract:

    Solver for regexes 

Author:

    Nikolaj Bjorner (nbjorner) 2020-5-22

--*/
#pragma once

#include "util/scoped_vector.h"
#include "util/uint_set.h"
#include "util/union_find.h"
#include "ast/seq_decl_plugin.h"
#include "ast/rewriter/seq_rewriter.h"
#include "smt/smt_context.h"
#include "smt/seq_skolem.h"

namespace smt {

    class theory_seq;

    class seq_regex;

    /*
        state_graph

        Data structure which is capable of incrementally tracking
        live states and dead states.

        "States" are integers. States and edges are added to the data
        structure incrementally.
        - States can be marked as live
          or as done -- to indicate that no more outgoing edges will be
          added and the state will not be marked as live. The data
          structure then tracks
          which other states are live (can reach a live state), dead
          (can't reach a live state), or neither.
        - Some edges are labeled as not contained in a cycle. This is to
          optimize search if it is known by the user of the structure
          that no cycle will ever contain this edge.

        Internally, we use union_find to identify states within an SCC,
        and incrementally update SCCs, while propagating backwards
        live and dead SCCs.
    */
    class state_graph {
        typedef unsigned           state;
        typedef uint_set           state_set;
        typedef u_map<state_set>   edge_rel;
        typedef basic_union_find   state_ufind;

    private:
        /*
            All states are internally exactly one of:
            - live:       known to reach a live state
            - dead:       known to never reach a live state
            - unknown:    all outgoing edges have been added, but the
                          state is not known to be live or dead
            - unexplored: not all outgoing edges have been added

            As SCCs are merged, some states become aliases, and a
            union find data structure collapses a now obsolete
            state to its current representative. m_seen keeps track
            of states we have seen, including obsolete states.

            Invariants:
            - TODO
        */
        state_set   m_live;
        state_set   m_dead;
        state_set   m_unknown;
        state_set   m_unexplored;

        state_set     m_seen;
        state_ufind   m_state_ufind;

        /*
            Edges are saved in both from and to maps.
            A subset of edges are also marked as possibly being
            part of a cycle by being stored in m_sources_maybecycle.

            Invariants:
            - TODO
        */
        edge_rel   m_sources;
        edge_rel   m_targets;
        edge_rel   m_sources_maybecycle;

        /*
            'Core' functions that modify the plain graph, without
            updating SCCs or propagating live/dead state information.
            These are for internal use only.
        */
        void add_state_core(state s);    // unexplored + seen
        void remove_state_core(state s); // unknown + seen -> seen
        void mark_unknown_core(state s); // unexplored -> unknown
        void mark_live_core(state s);    // unknown -> live
        void mark_dead_core(state s);    // unknown -> dead

        void add_edge_core(state s1, state s2, bool maybecycle);
        void remove_edge_core(state s1, state s2);
        void rename_edge_core(state old1, state old2, state new1, state new2);

        state merge_states(state s1, state s2);
        state merge_states(state_set& s_set);

        /*
            Algorithmic search routines
            - live state propagation
            - dead state propagation
            - cycle / strongly-connected component detection
        */
        void mark_live_recursive(state s);
        void mark_dead_recursive(state s);
        state merge_all_cycles(state s);

    public:
        state_graph():
            m_live(), m_dead(), m_unknown(), m_unexplored(), m_seen(),
            m_state_ufind(), m_sources(), m_targets(), m_sources_maybecycle() {}

        /*
            Exposed methods

            These methods may be called in any order, as long as:
            - states are added before edges are added between them
            - outgoing edges are not added from a done state
            - a done state is not marked as live
            - edges are not added creating a cycle containing an edge with
              maybecycle = false (this is not necessary for soundness, but
              prevents completeness for successfully detecting dead states)
        */
        void add_state(state s);
        void add_edge(state s1, state s2, bool maybecycle);
        void mark_live(state s);
        void mark_done(state s);

        bool is_seen(state s);
        bool is_live(state s);
        bool is_dead(state s);
        bool is_done(state s);

        unsigned get_size();

        /*
            Pretty printing
        */
        void pretty_print(std::ostream& o);

    };

    class seq_regex {
        /*
            Data about a constraint of the form (str.in_re s R)
        */
        struct s_in_re {
            literal m_lit;
            expr*   m_s;
            expr*   m_re;
            bool    m_active;
        s_in_re(literal l, expr* s, expr* r):
            m_lit(l), m_s(s), m_re(r), m_active(true) {}
        };

        /*
            Data about a literal for the solver to propagate
            The trigger guards whether the literal is ready
            to be addressed yet -- see seq_regex::can_propagate
        */
        struct propagation_lit {
            literal m_lit;
            literal m_trigger;
            propagation_lit(literal lit, literal t): m_lit(lit), m_trigger(t) {}
            propagation_lit(literal lit): m_lit(lit), m_trigger(null_literal) {}
            propagation_lit(): m_lit(null_literal), m_trigger(null_literal) {}
        };

        theory_seq&                      th;
        context&                         ctx;
        ast_manager&                     m;
        vector<s_in_re>                  m_s_in_re;
        scoped_vector<propagation_lit>   m_to_propagate;

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

        // Printing for seq_regex_brief
        std::string state_str(expr* e);
        std::string expr_id_str(expr* e);

        // ********************

        seq_util& u();
        class seq_util::re& re();
        class seq_util::str& str();
        seq_rewriter& seq_rw();
        seq_skolem& sk();
        arith_util& a();

        bool is_string_equality(literal lit);

        void rewrite(expr_ref& e);

        bool coallesce_in_re(literal lit);

        bool propagate(literal lit, literal& trigger);

        bool block_unfolding(literal lit, unsigned i);

        void propagate_nullable(literal lit, expr* s, unsigned idx, expr* r);

        bool propagate_derivative(literal lit, expr* e, expr* s, expr* i, unsigned idx, expr* r, literal& trigger);

        expr_ref mk_first(expr* r, expr* n);

        expr_ref unroll_non_empty(expr* r, expr_mark& seen, unsigned depth);

        bool is_member(expr* r, expr* u);

        expr_ref symmetric_diff(expr* r1, expr* r2);

        expr_ref is_nullable_wrapper(expr* r);
        expr_ref derivative_wrapper(expr* hd, expr* r);

        void get_cofactors(expr* r, expr_ref_vector& conds, expr_ref_pair_vector& result);

        void get_cofactors(expr* r, expr_ref_pair_vector& result) {
            expr_ref_vector conds(m);
            get_cofactors(r, conds, result);
        }

    public:

        void get_all_derivatives(expr* r, expr_ref_vector& results);

        seq_regex(theory_seq& th);

        void push_scope() { m_to_propagate.push_scope(); }

        void pop_scope(unsigned num_scopes) { m_to_propagate.pop_scope(num_scopes); }

        bool can_propagate() const;

        bool propagate();

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
