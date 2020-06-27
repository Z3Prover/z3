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

    class seq_regex {
        /*
            seen_states

            Info saved about the set of states (regexes) seen so far.

            "States" here are strongly connected components -- states that
            are mutually reachable from each other. States
            are represented as unsigned integers.

            Used for the core incremental dead state elimination algorithm.

            Class invariants:
                - TODO
        */
        class seen_states {
            typedef unsigned              state;
            typedef uint_set              state_set;
            typedef uint_map<state_set>   edge_rel;
            typedef basic_union_find      state_ufind;
            // typedef uint_map<expr_ref_vector>  exprs_of_state;

        private:
            /*
                All states are exactly one of:
                - alive:      known to be nonempty
                - dead:       known to be empty
                - unknown:    all outgoing transitions have been
                              seen, but the state is not known
                              to be alive or dead
                - unvisited:  not all outgoing transitions have
                              been seen

                The set m_seen keeps all of these and in addition,
                seen states that have been merged and no longer reprsent
                a current SCC.
            */
            state_set   m_seen;
            state_set   m_alive;
            state_set   m_dead;
            state_set   m_unknown;
            state_set   m_unvisited;

            void mark_unknown(state s); // unvisited -> unknown
            void mark_alive(state s);   // unknown -> alive
            void mark_dead(state s);    // unknown -> dead

            bool is_resolved(state s);   // alive or dead
            bool is_unresolved(state s); // unknown or unvisited

            /*
                Initially a state is represented by an expression ID.
                A union find data structure collapses an ID to a state.

                Edges are saved in both from and to maps.
                Additionally edges from are divided into those possibly
                in a cycle, and those not in a cycle.
            */
            state_ufind   m_state_ufind;

            state get_state(expr* e);
            state merge_states(state s1, state s2);
            state merge_states(state_set& s_set);

            edge_rel      m_from_cycle;
            edge_rel      m_from_nocycle;
            edge_rel      m_to;

            /*
                Caching details
            */
            unsigned          m_max_size { 10000 };
            expr_ref_vector   m_trail;

            /*
                Core cycle-detection routine
            */
            // Heuristic on syntactic expressions
            bool can_be_in_cycle(expr* e1, expr* e2);
            // Full check: if new edge (s1, s2) will create at least one cycle,
            // merge all states in the new SCC
            void find_and_merge_cycles(state s1, state s2);

        public:
            /*
                Main exposed methods:
                - adding a state
                - adding a transition from a state
                - checking if a state is known to be alive or dead
            */
            void add_state(expr* e);
            void add_transition(expr* e1, expr* e2);
            bool is_alive(expr* e);
            bool is_dead(expr* e);

            seen_states(ast_manager& m):
                m_seen(), m_alive(), m_dead(), m_unknown(), m_unvisited(),
                m_state_ufind(), m_from_cycle(), m_from_nocycle(), m_to(),
                m_trail(m) {}
        };

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

        theory_seq&      th;
        context&         ctx;
        ast_manager&     m;
        vector<s_in_re> m_s_in_re;
        scoped_vector<propagation_lit> m_to_propagate;

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

