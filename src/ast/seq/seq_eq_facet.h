/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_eq_facet.h

Abstract:

    Word equations are stored as token lists: each side of a `str.++`
    chain is flattened into a vector of length-1 string constants and
    opaque non-constant terms.

    `eq_facet::simplify` performs deterministic reductions such as
    stripping common prefixes/suffixes, detecting symbol clashes, and
    forcing `v := epsilon` when one side is empty.

    `word_eq_split` performs the remaining Nielsen-style branching for
    variable/constant and variable/variable heads or tails.

Author:

    Nikolaj Bjorner (nbjorner) 2026
    Clemens Eisenhofer 2026
    Margus Veanes 2026

--*/
#pragma once

#include "ast/ast.h"
#include "ast/seq_decl_plugin.h"
#include "ast/seq/seq_ambient_context.h"
#include "ast/seq/seq_assumption_facet.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/seq/seq_eq_approx.h"
#include "util/stx_search_tree.h"
#include "util/trail.h"
#include <algorithm>

namespace seq {

    // Dependency source leaf type for this search tree instantiation.
    using eq_tree = stx::search_tree<unsigned>;

    // A flattened side of a word equation is represented directly as an
    // `expr_ref_vector`: a sequence of tokens, each either a length-1
    // string constant or an opaque variable/term. Reference-counted
    // (rather than a raw ptr_vector<expr>) since tokens may be
    // freshly-created variables (e.g. from mk_fresh_var) that nothing
    // else in the system is holding a reference to.

    // Tokens are obtained directly via `u.str.get_concat_units(e, out)`:
    // constants are exploded into one token per character; any other
    // leaf (variable or otherwise-opaque term) becomes a single token.

    // Recover the node's ambient context as an ambient_ref.
    ambient_ref<eq_tree::node, eq_tree::dep_tracker> get_ambient(eq_tree::node& n);
    ambient_ref<eq_tree::node const, eq_tree::dep_tracker> get_ambient(eq_tree::node const& n);

    // Replace every occurrence of `var` in `ts` with the tokens of `repl`
    // (order-preserving splice). Shared helper between `eq_facet` and
    // `deq_facet` (and any future facet holding token-list equations).
    void subst_in(expr_ref_vector& ts, expr* var, expr_ref_vector const& repl);

    // Mixin for facets that must stay synchronized with token
    // substitutions chosen elsewhere.
    class subst_sink_i {
    public:
        virtual ~subst_sink_i() = default;
        // `subst_dep` justifies the substitution itself. Each sink joins
        // it into the dependencies of the constraints it mutates.
        virtual void apply_subst(expr* var, expr_ref_vector const& repl, eq_tree::dep_tracker subst_dep) = 0;
    };

    // Trail undo object for a single-element `vector<T>::erase(idx)`.
    template <typename T>
    class vector_erase_trail : public ::trail {
        vector<T>& m_vec;
        unsigned   m_idx;
        T          m_value;
    public:
        vector_erase_trail(vector<T>& v, unsigned idx) : m_vec(v), m_idx(idx), m_value(v[idx]) {}
        void undo() override {
            // Grow by one, shift elements up, then restore the erased slot.
            m_vec.push_back(m_value);
            for (unsigned i = m_vec.size() - 1; i > m_idx; --i)
                m_vec[i] = std::move(m_vec[i - 1]);
            m_vec[m_idx] = std::move(m_value);
        }
    };

    // Like value_trail<T>, but restores a field of a vector element by
    // index so later reallocation does not invalidate the target.
    template <typename Elem, typename T>
    class vector_field_trail : public ::trail {
        vector<Elem>& m_vec;
        unsigned      m_idx;
        T Elem::*     m_member;
        T             m_old_value;
    public:
        vector_field_trail(vector<Elem>& v, unsigned idx, T Elem::* member)
            : m_vec(v), m_idx(idx), m_member(member), m_old_value(v[idx].*member) {}
        void undo() override {
            m_vec[m_idx].*m_member = std::move(m_old_value);
        }
    };

    // If `var` occurs in the selected token vector, trail and perform the
    // substitution; otherwise return false.
    template <typename Elem>
    inline bool subst_in_trailed(trail_stack& trail, vector<Elem>& vec, unsigned idx, expr_ref_vector Elem::* member, expr* var, expr_ref_vector const& repl) {
        expr_ref_vector& ts = vec[idx].*member;
        bool present = false;
        for (expr* t : ts)
            if (t == var) { present = true; break; }
        if (!present)
            return false;
        trail.push(vector_field_trail<Elem, expr_ref_vector>(vec, idx, member));
        subst_in(ts, var, repl);
        return true;
    }

    /**
     * Facet holding a set of pending word equations. Equations are
     * discharged (removed) as soon as they are solved; the facet is
     * satisfied when the set is empty.
     */
    class eq_facet : public stx::facet_i, public subst_sink_i {
    public:
        struct subst_entry {
            expr_ref         m_var;
            expr_ref_vector  m_repl;
            subst_entry(ast_manager& m, expr* var, expr_ref_vector const& repl) :
                m_var(var, m), m_repl(repl) {}
        };
        struct equation : public stx::constraint_i {
            expr_ref_vector      m_lhs;
            expr_ref_vector      m_rhs;
            eq_tree::dep_tracker m_dep;
            bool                 m_active = true;
            equation(expr_ref_vector const& lhs, expr_ref_vector const& rhs, eq_tree::dep_tracker dep = nullptr) :
                m_lhs(lhs), m_rhs(rhs), m_dep(dep) {}
            bool active() const { return m_active; }

            // -- stx::constraint_i (unsat-cache identity) --
            // Canonicalize (lhs,rhs) so mirrored equations compare equal.
            // clone() keeps only the value part of the constraint.
            uint64_t hash() const override;
            bool equals(stx::constraint_i const& other) const override;
            stx::constraint_i* clone() const override { return alloc(equation, m_lhs, m_rhs); }
            // Expose the justification so conflict cores can be filtered.
            void* dep_handle() const override { return m_dep; }
        };


    private:
        ast_manager&          m;
        seq_util&             u;
        seq_rewriter          m_rw;
        eq_tree::dep_manager_t& m_dm;
        vector<equation>      m_eqs;
        vector<subst_entry>   m_subst;

    public:
        eq_facet(trail_stack& trail, ast_manager& m, seq_util& u, eq_tree::dep_manager_t& dm) :
            facet_i(trail), m(m), u(u), m_rw(m), m_dm(dm) {}

        ast_manager& get_manager() const { return m; }
        seq_util& get_seq_util() const { return u; }
        eq_tree::dep_manager_t& dm() const { return m_dm; }

        // Trailed equation insertion.
        void add_equation(expr_ref_vector const& lhs, expr_ref_vector const& rhs, eq_tree::dep_tracker dep = nullptr) {
            m_eqs.push_back(equation(lhs, rhs, dep));
            m_trail.push(push_back_trail<equation>(m_eqs));
        }
        // Convenience overload that tokenizes lhs and rhs first.
        void add_equation(expr* lhs, expr* rhs, eq_tree::dep_tracker dep = nullptr) {
            expr_ref_vector lts(m), rts(m);
            u.str.get_concat_units(lhs, lts);
            u.str.get_concat_units(rhs, rts);
            add_equation(lts, rts, dep);
        }

        void remove_equation_trailed(unsigned idx) {
            m_trail.push(vector_field_trail<equation, bool>(m_eqs, idx, &equation::m_active));
            m_eqs[idx].m_active = false;
        }

        vector<equation> const& equations() const { return m_eqs; }
        vector<subst_entry> const& substitutions() const { return m_subst; }

        // Append-only substitution table used during model construction.
        // Walking it backwards yields the newest active binding.
        bool get_subst(expr* var, expr_ref_vector& out) const;
        void eliminate(expr* e, expr_ref_vector& out) const;
        void eliminate(expr_ref_vector const& in, expr_ref_vector& out) const;

        // Allocate a fresh opaque variable token of `s`'s sort.
        expr* mk_fresh_var(sort* s) { return m.mk_fresh_const("t", s); }

        // -- stx::facet_i --
        facet_i* clone(trail_stack& trail) const override;

        bool is_satisfied() const override { return std::all_of(m_eqs.begin(), m_eqs.end(), [](equation const& e) { return !e.active(); }); }
        std::ostream& display(std::ostream& out) const override;

        // -- unsat-cache signature --
        // Word equations directly determine (in)consistency in the
        // Nielsen transformation, so they always participate.
        bool contributes_to_signature() const override { return true; }
        void append_constraints(vector<stx::constraint_i const*>& out) const override;

        // Deterministic simplification pass over all active equations.
        // On conflict, `conflict_dep` identifies the culprit equation.
        bool simplify(eq_tree::node& n, ambient_context_i<eq_tree::dep_tracker>& ac, bool& conflict, eq_tree::dep_tracker& conflict_dep);
        ambient_context_i<eq_tree::dep_tracker>& ambient(eq_tree::node const& n) const;

    private:
        void apply_subst(expr* var, expr_ref_vector const& repl, eq_tree::dep_tracker subst_dep) override;

        bool simplify_equation(eq_tree::node& n, ambient_context_i<eq_tree::dep_tracker>& ac, unsigned idx, bool& conflict, eq_tree::dep_tracker& conflict_dep, bool& changed);
    };

    void broadcast_subst(eq_tree::node& target, expr* var, expr_ref_vector const& repl, eq_tree::dep_tracker subst_dep);

    // Deterministic propagation plugin wrapping eq_facet::simplify.
    class eq_propagation : public eq_tree::propagation_plugin_i {
        ast_manager& m;
        seq_util&    u;
        struct stats {
            unsigned m_num_propagate = 0;
            unsigned m_num_progress  = 0;
            void reset() { *this = stats(); }
        };
        stats m_stats;
    public:
        eq_propagation(ast_manager& m, seq_util& u) : m(m), u(u) {}
        char const* name() const override { return "eq-propagate"; }
        stx::simplify_result propagate(eq_tree::node& n) override;
        void collect_statistics(::statistics& st) const override {
            st.update("seq-eq-propagate num calls", m_stats.m_num_propagate);
            st.update("seq-eq-propagate num progress", m_stats.m_num_progress);
        }
        void reset_statistics() override { m_stats.reset(); }
    };

    // Nielsen-transformation split plugin. It examines both ends of an
    // equation so suffix-only branching opportunities are not missed.
    class word_eq_split : public eq_tree::split_plugin_i {
        ast_manager& m;
        seq_util&    u;
        struct stats {
            unsigned m_num_splits = 0;
            void reset() { *this = stats(); }
        };
        stats m_stats;

        class iterator : public eq_tree::split_iterator_i {
            eq_tree::node& m_n;
            ast_manager&   m;
            seq_util&      u;
            // Remaining alternatives to produce, in order.
            struct alt { char const* m_name; expr_ref m_var; expr_ref_vector m_repl; eq_tree::dep_tracker m_dep; expr_ref m_guard; bool m_progress; };
            vector<alt>    m_pending;
            unsigned       m_pos = 0;
        public:
            iterator(eq_tree::node& n, ast_manager& m, seq_util& u) : m_n(n), m(m), u(u) {}
            // `progress` is false for alternatives that introduce a fresh variable.
            void push_back(char const* name, expr* var, expr_ref_vector const& repl, eq_tree::dep_tracker dep, expr* guard = nullptr, bool progress = true) {
                m_pending.push_back(alt{ name, expr_ref(var, m), repl, dep, expr_ref(guard, m), progress });
            }
            bool next(eq_tree::edge& out) override;
        };

    public:
        word_eq_split(ast_manager& m, seq_util& u) : m(m), u(u) {}
        char const* name() const override { return "nielsen-split"; }
        scoped_ptr<eq_tree::split_iterator_i> split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) override;
        void collect_statistics(::statistics& st) const override { st.update("seq-nielsen-split num splits", m_stats.m_num_splits); }
        void reset_statistics() override { m_stats.reset(); }
    };

    // Refutation-only split plugin that uses seq_eq_approx::check. It
    // never produces branches: it either reports a conflict or declines.
    class eq_approx_split : public eq_tree::split_plugin_i {
        ast_manager&    m;
        seq_util&       u;
        seq_rewriter&   m_rw;
        seq_eq_approx   m_approx;
        struct stats {
            unsigned m_num_checks = 0;
            unsigned m_num_refuted = 0;
            void reset() { *this = stats(); }
        };
        stats m_stats;
    public:
        eq_approx_split(ast_manager& m, seq_util& u, seq_rewriter& rw,
                        unsigned max_states = 1u << 12) :
            m(m), u(u), m_rw(rw), m_approx(rw, max_states) {
            set_min_cost(0);
        }
        char const* name() const override { return "eq-approx-split"; }
        scoped_ptr<eq_tree::split_iterator_i> split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) override;
        void collect_statistics(::statistics& st) const override {
            st.update("seq-eq-approx-split num checks", m_stats.m_num_checks);
            st.update("seq-eq-approx-split num refuted", m_stats.m_num_refuted);
        }
        void reset_statistics() override { m_stats.reset(); }
    };

    // Deterministic interior split with an optional padding variable.
    // It cuts an equation at a balanced point and replaces it with two
    // shorter equations plus the necessary length constraints.
    class eq_split : public eq_tree::split_plugin_i {
        ast_manager&  m;
        seq_util&     u;
        struct stats {
            unsigned m_num_splits = 0;
            void reset() { *this = stats(); }
        };
        stats m_stats;

        // Tokens from get_concat_units are either unit constants or
        // variable-length opaque terms.
        static bool token_has_variable_length(seq_util& u, expr* tok) { return !u.str.is_unit(tok); }

    public:
        eq_split(ast_manager& m, seq_util& u) : m(m), u(u) {}
        char const* name() const override { return "eq-split"; }

        // Find a balanced interior split point, if one exists.
        static bool find_eq_split_point(seq_util& u, expr_ref_vector const& lhs, expr_ref_vector const& rhs,
                                         unsigned& out_lhs_idx, unsigned& out_rhs_idx, int& out_padding);

        scoped_ptr<eq_tree::split_iterator_i> split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) override;
        void collect_statistics(::statistics& st) const override { st.update("seq-eq-split num splits", m_stats.m_num_splits); }
        void reset_statistics() override { m_stats.reset(); }
    };

    /**
     * Facet holding pending word disequations (`lhs != rhs`). It reacts
     * to substitutions broadcast from other facets, discharges a
     * disequation once distinct leading constants are exposed, and
     * reports a conflict if both sides reduce to empty.
     */
    class deq_facet : public stx::facet_i, public subst_sink_i {
    public:
        struct disequation : public stx::constraint_i {
            expr_ref_vector      m_lhs;
            expr_ref_vector      m_rhs;
            eq_tree::dep_tracker m_dep;
            bool                 m_active = true;
            disequation(expr_ref_vector const& lhs, expr_ref_vector const& rhs, eq_tree::dep_tracker dep = nullptr) :
                m_lhs(lhs), m_rhs(rhs), m_dep(dep) {}
            bool active() const { return m_active; }

            // -- stx::constraint_i (unsat-cache identity) --
            // Same canonicalization as equations, but a disequation is a
            // distinct constraint kind.
            uint64_t hash() const override;
            bool equals(stx::constraint_i const& other) const override;
            stx::constraint_i* clone() const override { return alloc(disequation, m_lhs, m_rhs); }
            void* dep_handle() const override { return m_dep; }
        };

    private:
        ast_manager& m;
        seq_util&    u;
        seq_rewriter m_rw;
        eq_tree::dep_manager_t& m_dm;
        vector<disequation> m_diseqs;

    public:
        deq_facet(trail_stack& trail, ast_manager& m, seq_util& u, eq_tree::dep_manager_t& dm) :
            facet_i(trail), m(m), u(u), m_rw(m), m_dm(dm) {}

        ast_manager& get_manager() const { return m; }
        seq_util& get_seq_util() const { return u; }

        // Trailed disequation insertion.
        void add_disequation(expr_ref_vector const& lhs, expr_ref_vector const& rhs, eq_tree::dep_tracker dep = nullptr) {
            m_diseqs.push_back(disequation(lhs, rhs, dep));
            m_trail.push(push_back_trail<disequation>(m_diseqs));
        }

        vector<disequation> const& disequations() const { return m_diseqs; }

        // Apply a broadcast substitution to every pending disequation.
        void apply_subst(expr* var, expr_ref_vector const& repl, eq_tree::dep_tracker subst_dep) override;

        // Trailed removal of the disequation at `idx`.
        void remove_disequation_trailed(unsigned idx) {
            m_trail.push(vector_field_trail<disequation, bool>(m_diseqs, idx, &disequation::m_active));
            m_diseqs[idx].m_active = false;
        }

        // -- stx::facet_i --
        facet_i* clone(trail_stack& trail) const override;
        bool is_satisfied() const override { return std::all_of(m_diseqs.begin(), m_diseqs.end(), [](disequation const& d) { return !d.active(); }); }
        std::ostream& display(std::ostream& out) const override;

        // -- unsat-cache signature --
        bool contributes_to_signature() const override { return true; }
        void append_constraints(vector<stx::constraint_i const*>& out) const override;

        // Deterministic simplification pass over all active disequations.
        bool simplify(bool& conflict, eq_tree::dep_tracker& conflict_dep);
    };

    // Deterministic propagation plugin wrapping deq_facet::simplify.
    class deq_propagation : public eq_tree::propagation_plugin_i {
        ast_manager& m;
        seq_util&    u;
        struct stats {
            unsigned m_num_propagate = 0;
            void reset() { *this = stats(); }
        };
        stats m_stats;
    public:
        deq_propagation(ast_manager& m, seq_util& u) : m(m), u(u) {}
        char const* name() const override { return "deq-propagate"; }
        stx::simplify_result propagate(eq_tree::node& n) override;
        void collect_statistics(::statistics& st) const override { st.update("seq-deq-propagate num calls", m_stats.m_num_propagate); }
        void reset_statistics() override { m_stats.reset(); }
    };


    // Split plugin for unresolved disequations. It branches on the two
    // possible strict length orders, or on an equal-length
    // decomposition that reduces the disequation to a differing
    // character.
    class deq_split : public eq_tree::split_plugin_i {
        ast_manager&  m;
        seq_util&     u;
        struct stats {
            unsigned m_num_splits = 0;
            void reset() { *this = stats(); }
        };
        stats m_stats;

        // Remaining alternatives after the first materialized branch.
        class iterator : public eq_tree::split_iterator_i {
            eq_tree::node& m_n;
            unsigned       m_diseq_idx;
            expr_ref_vector m_lhs, m_rhs; // original sides before branch mutation
            eq_tree::dep_tracker m_dep;
            unsigned       m_next_case; // 2, then 3, then done
            ast_manager&   m;
            seq_util&      u;
        public:
            iterator(eq_tree::node& n,
                      unsigned diseq_idx, expr_ref_vector const& lhs, expr_ref_vector const& rhs,
                      eq_tree::dep_tracker dep, unsigned next_case, ast_manager& m, seq_util& u) :
                m_n(n),
                m_diseq_idx(diseq_idx), m_lhs(lhs), m_rhs(rhs), m_dep(dep), m_next_case(next_case), m(m), u(u) {}
            bool next(eq_tree::edge& out) override;
        };

    public:
        deq_split(ast_manager& m, seq_util& u) : m(m), u(u) {}
        char const* name() const override { return "deq-split"; }
        scoped_ptr<eq_tree::split_iterator_i> split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) override;
        void collect_statistics(::statistics& st) const override { st.update("seq-deq-split num splits", m_stats.m_num_splits); }
        void reset_statistics() override { m_stats.reset(); }
    };

} // namespace seq
