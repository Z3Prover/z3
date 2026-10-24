/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_landing.h

Abstract:

    Landing decomposition of regex memberships over the explored part G of the
    derivative automaton (seq_deriv_graph.h).  Pins are single-variable gated
    views in mem_facet, so their joint feasibility and witnesses come from
    mem_facet's view_witness.  The equation side is reached only through
    broadcast_subst, arithmetic only through the solver facet.

    A character that stands for a class of characters is a token unit(c) with a
    fresh character constant c, constrained by the primitive membership
    [unit(c)] in <class>.  A derivative step over it is taken when the whole
    class leads to one state; otherwise mem_char_split splits the class by
    successor.

      landing_propagation  derivative steps on gated views, their discharge,
                           substitution of variables pinned to {epsilon},
                           length abstraction of gated views, conflict
                           detection Omega(u) /\ r = {}.  Plain memberships
                           are left as asserted.
      eq_lang_propagation  optional: Omega(u) /\ Omega(v) = {} refutes u = v.
                           The only rule that reads equations and pins.
      mem_char_split       splits the class of a symbolic character by the
                           successors of the state it is read in.
      mem_landing_split    derivative steps on plain memberships (recording G),
                           subsumption, probes, and the land / escape branches;
                           unwinding (the region {r}) at heads that are not on
                           a cycle of G.  All memberships the variable leads
                           land together, over the product of their regions.

    G is owned by landing_propagation and outlives every view built over it.

Author:

    Clemens Eisenhofer 2026

--*/
#pragma once

#include "ast/seq/seq_mem_facet.h"
#include "ast/seq/seq_deriv_graph.h"

namespace seq {

    class landing_propagation : public eq_tree::propagation_plugin_i {
        ast_manager& m;
        seq_util&    u;
        deriv_graph  m_graph;
        unsigned     m_qhead = 0;
        unsigned     m_checked = 0;
        struct stats {
            unsigned m_num_steps = 0;
            unsigned m_num_length = 0;
            unsigned m_num_conflicts = 0;
            void reset() { *this = stats(); }
        };
        stats m_stats;

        bool conflict(eq_tree::node& n);

    public:
        landing_propagation(ast_manager& m, seq_util& u, seq_rewriter& rw) : m(m), u(u), m_graph(rw) {}
        deriv_graph& graph() { return m_graph; }
        char const* name() const override { return "landing"; }
        stx::simplify_result propagate(eq_tree::node& n) override;
        void collect_statistics(::statistics& st) const override {
            st.update("seq-landing num steps", m_stats.m_num_steps);
            st.update("seq-landing num length", m_stats.m_num_length);
            st.update("seq-landing num conflicts", m_stats.m_num_conflicts);
        }
        void reset_statistics() override { m_stats.reset(); }
    };

    class eq_lang_propagation : public eq_tree::propagation_plugin_i {
        seq_util&    u;
        deriv_graph& m_graph;
        unsigned     m_mark = UINT_MAX;
        unsigned     m_num_conflicts = 0;
    public:
        eq_lang_propagation(seq_util& u, deriv_graph& g) : u(u), m_graph(g) {}
        char const* name() const override { return "eq-lang"; }
        stx::simplify_result propagate(eq_tree::node& n) override;
        void collect_statistics(::statistics& st) const override { st.update("seq-eq-lang num conflicts", m_num_conflicts); }
        void reset_statistics() override { m_num_conflicts = 0; }
    };

    class mem_char_split : public eq_tree::split_plugin_i {
        ast_manager& m;
        seq_util&    u;
        deriv_graph& m_graph;
        unsigned     m_num_splits = 0;

        class iterator : public eq_tree::split_iterator_i {
            eq_tree::node&          m_n;
            ast_manager&            m;
            seq_util&               u;
            expr_ref                m_tok;
            eq_tree::dep_tracker    m_dep;
            vector<range_predicate> m_parts;
            unsigned                m_pos = 0;
        public:
            iterator(eq_tree::node& n, ast_manager& m, seq_util& u, expr* tok, eq_tree::dep_tracker dep, vector<range_predicate> const& parts) :
                m_n(n), m(m), u(u), m_tok(tok, m), m_dep(dep), m_parts(parts) {}
            bool next(eq_tree::edge& out) override;
        };

    public:
        mem_char_split(ast_manager& m, seq_util& u, deriv_graph& g) : m(m), u(u), m_graph(g) {}
        char const* name() const override { return "mem-char"; }
        scoped_ptr<eq_tree::split_iterator_i> split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) override;
        void collect_statistics(::statistics& st) const override { st.update("seq-landing num char splits", m_num_splits); }
        void reset_statistics() override { m_num_splits = 0; }
    };

    class mem_landing_split : public eq_tree::split_plugin_i {
        // a membership the landing decomposes; all members share their leading variable
        struct member {
            unsigned        m_idx;
            unsigned        m_origin;
            expr_ref_vector m_str;
            view            m_view;
            region const*   m_gate = nullptr;
            member(unsigned idx, str_mem const& sm) :
                m_idx(idx), m_origin(sm.m_origin), m_str(sm.m_str), m_view(sm.m_view) {}
        };
        struct branch {
            enum kind_t { probe, subsume, land, escape } m_kind;
            ptr_vector<expr> m_states;           // land: landing state, escape: frontier state, per member
            bool             m_eps = false;      // probe x = epsilon
            range_predicate  m_chars;            // probe, escape: the characters read
        };
        struct stats {
            unsigned m_num_splits = 0;
            unsigned m_num_steps = 0;
            unsigned m_num_joint = 0;
            unsigned m_num_unwind = 0;
            unsigned m_num_subsumed = 0;
            void reset() { *this = stats(); }
        };

        ast_manager& m;
        seq_util&    u;
        deriv_graph& m_graph;
        unsigned     m_product_budget = 2000;
        stats        m_stats;

        class iterator : public eq_tree::split_iterator_i {
            eq_tree::node&       m_n;
            ast_manager&         m;
            seq_util&            u;
            vector<member>       m_members;
            eq_tree::dep_tracker m_dep;
            vector<branch>       m_branches;
            unsigned             m_pos = 0;
        public:
            iterator(eq_tree::node& n, ast_manager& m, seq_util& u, vector<member> const& ms, eq_tree::dep_tracker dep, vector<branch> const& bs) :
                m_n(n), m(m), u(u), m_members(ms), m_dep(dep), m_branches(bs) {}
            bool next(eq_tree::edge& out) override;
        };

        bool mk_member(eq_tree::node& n, member& mb, bool cyclic_only);
        bool product(vector<member> const& ms, vector<ptr_vector<expr>>& lands, vector<std::pair<ptr_vector<expr>, range_predicate>>& escapes);
        bool mk_branches(eq_tree::node& n, unsigned idx, bool cyclic_only, vector<member>& ms, eq_tree::dep_tracker& dep, vector<branch>& bs);

    public:
        mem_landing_split(ast_manager& m, seq_util& u, deriv_graph& g) : m(m), u(u), m_graph(g) {}
        char const* name() const override { return "mem-landing"; }
        scoped_ptr<eq_tree::split_iterator_i> split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) override;
        void collect_statistics(::statistics& st) const override {
            st.update("seq-landing num splits", m_stats.m_num_splits);
            st.update("seq-landing num split steps", m_stats.m_num_steps);
            st.update("seq-landing num joint", m_stats.m_num_joint);
            st.update("seq-landing num unwind", m_stats.m_num_unwind);
            st.update("seq-landing num subsumed", m_stats.m_num_subsumed);
        }
        void reset_statistics() override { m_stats.reset(); }
    };

}
