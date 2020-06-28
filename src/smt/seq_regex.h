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
#include "util/uint_map.h"
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

        Data structure which calculates live states and dead states.

        ----

        Info saved about the set of states (regexes) seen so far.

        "States" here are strongly connected components -- states that
        are mutually reachable from each other. States
        are represented as unsigned integers.

        Used for the core incremental dead state elimination algorithm.

        Class invariants:
            - TODO
    */
    class state_graph {
        typedef unsigned              state;
        typedef uint_set              state_set;
        typedef uint_map<state_set>   edge_rel;
        typedef basic_union_find      state_ufind;
        // typedef uint_map<expr_ref_vector>  exprs_of_state;

    private:
        ast_manager& m;
        seq_regex& m_parent;

        /*
            All states are exactly one of:
            - live:       known to be nonempty
            - dead:       known to be empty
            - unknown:    all outgoing transitions have been
                          added, but the state is not known
                          to be live or dead
            - unvisited:  outgoing transitions have not been added

            As SCCs are merged, some states become aliases, and a
            union find data structure collapses a now obsolete
            state to its current representative. m_seen keeps track
            of states we have seen, including obsolete states.
        */
        state_set   m_live;
        state_set   m_dead;
        state_set   m_unknown;
        state_set   m_unvisited;

        state_set     m_seen;
        state_ufind   m_state_ufind;

        void add_state(state s);    // unvisited + seen
        void remove_state(state s); // * -> m_seen only

        void mark_unknown(state s); // unvisited -> unknown
        void mark_live(state s);    // unknown -> live
        void mark_dead(state s);    // unknown -> dead

        // bool is_resolved(state s);   // live or dead
        // bool is_unresolved(state s); // unknown or unvisited

        /*
            Edges are saved in both from and to maps.
            A subset of edges are also marked as possibly being
            part of a cycle by being stored in m_from_maybecycle.
        */
        edge_rel   m_from;
        edge_rel   m_to;
        edge_rel   m_from_maybecycle;

        void add_edge(state s1, state s2, bool maybecycle);
        void remove_edge(state s1, state s2);
        void rename_edge(state old1, state old2, state new1, state new2);

        state merge_states(state s1, state s2);
        state merge_states(state_set& s_set);

        /*
            Caching details
        */
        unsigned          m_max_size { 10000 };
        expr_ref_vector   m_trail;

        /*
            Core algorithmic search routines
            - live state propagation
            - dead state propagation
            - cycle detection
        */
        void mark_live_recursive(state s);
        void mark_dead_recursive(state s);
        state merge_all_cycles(state s1, state_set& s_to);

        /*
            Methods on original expressions (before they are turned
            into states)
        */
        // Convert expression to state
        state get_state(expr* e);
        // Cycle-detection heuristic (sound but not complete)
        bool can_be_in_cycle(expr* e1, expr* e2);

    public:
        /*
            Exposed methods:
            - adding a state and all its transitions
            - checking if a state is known to be live or dead
        */
        void add_state(expr* e, bool live);
        void add_all_transitions(expr* e1);
        bool is_live(expr* e);
        bool is_dead(expr* e);

        state_graph(ast_manager& m, seq_regex& parent):
            m(m), m_parent(parent),
            m_live(), m_dead(), m_unknown(), m_unvisited(), m_seen(),
            m_state_ufind(), m_from(), m_to(), m_from_maybecycle(),
            m_trail(m) {}
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
        state_graph                      m_state_graph;

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
