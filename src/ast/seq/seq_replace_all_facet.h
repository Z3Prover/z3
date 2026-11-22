/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_replace_all_facet.h

Abstract:

    `str.replace_all` with a non-empty literal pattern. The scan is
    leftmost, so a known prefix of the input can always be evaluated.

Author:

    Clemens Eisenhofer 2026

--*/
#pragma once

#include "ast/ast.h"
#include "ast/seq_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/seq/seq_eq_facet.h"
#include "util/stx_search_tree.h"
#include "util/trail.h"
#include <algorithm>

namespace seq {

    // The proof follows the current result/input/replacement tokens through substitutions.
    struct str_replace_all {
        expr_ref_vector      m_result;
        expr_ref_vector      m_input;
        expr_ref_vector      m_repl;
        expr_ref             m_pattern; // non-empty string literal
        eq_tree::dep_tracker m_dep;
        proof_ref            m_proof;
        bool                 m_active = true;
        str_replace_all(expr_ref_vector const& r, expr_ref_vector const& i, expr* p, expr_ref_vector const& t, eq_tree::dep_tracker dep, proof* pr = nullptr) :
            m_result(r), m_input(i), m_repl(t), m_pattern(p, r.get_manager()), m_dep(dep), m_proof(pr, r.get_manager()) {}
        expr_ref fact(seq_util& u) const;
        bool active() const { return m_active; }
    };

    // len(result) vs. len(input) for a constant replacement, null otherwise.
    expr_ref replace_all_length_relation(seq_util& u, arith_util& a, expr* result, expr* input, expr* pattern, expr_ref_vector const& repl);

    class replace_all_facet : public stx::facet_i, public subst_sink_i {
        ast_manager& m;
        eq_tree::dep_manager_t& m_dm;
        vector<str_replace_all> m_ras;

    public:
        replace_all_facet(trail_stack& trail, ast_manager& m, eq_tree::dep_manager_t& dm) :
            facet_i(trail), m(m), m_dm(dm) { dm.set_manager(m); }

        eq_tree::dep_manager_t& dm() const { return m_dm; }

        void add(expr_ref_vector const& r, expr_ref_vector const& i, expr* p, expr_ref_vector const& t, eq_tree::dep_tracker dep, proof* pr = nullptr, symbol rule = symbol("replace-all-input")) {
            str_replace_all ra(r, i, p, t, dep, pr);
            if (!pr && m_dm.proofs_enabled()) {
                seq_util u(m);
                ra.m_proof = m_dm.mk_proof(rule, ra.fact(u));
            }
            m_ras.push_back(ra);
            m_trail.push(push_back_trail<str_replace_all>(m_ras));
        }

        void remove(unsigned idx, symbol rule = symbol("replace-all-discharge"), proof* pr = nullptr);

        vector<str_replace_all> const& obligations() const { return m_ras; }

        void apply_subst(expr* var, expr_ref_vector const& repl, eq_tree::dep_tracker subst_dep) override;

        stx::facet_i* clone(trail_stack& trail) const override;
        bool is_satisfied() const override { return std::all_of(m_ras.begin(), m_ras.end(), [](str_replace_all const& ra) { return !ra.active(); }); }
        std::ostream& display(std::ostream& out) const override;
    };

    class replace_all_propagation : public eq_tree::propagation_plugin_i {
        ast_manager& m;
        seq_util&    u;
        struct stats {
            unsigned m_num_eval = 0;
            unsigned m_num_cut = 0;
            void reset() { *this = stats(); }
        };
        stats m_stats;
    public:
        replace_all_propagation(ast_manager& m, seq_util& u) : m(m), u(u) {}
        char const* name() const override { return "replace-all-propagate"; }
        stx::simplify_result propagate(eq_tree::node& n) override;
        void collect_statistics(::statistics& st) const override {
            st.update("seq-replace-all num evaluations", m_stats.m_num_eval);
            st.update("seq-replace-all num cuts", m_stats.m_num_cut);
        }
        void reset_statistics() override { m_stats.reset(); }
    };

    // Case split on how the input starts relative to the pattern.
    class replace_all_split : public eq_tree::split_plugin_i {
        ast_manager& m;
        seq_util&    u;
        struct stats {
            unsigned m_num_splits = 0;
            void reset() { *this = stats(); }
        };
        stats m_stats;

        class iterator : public eq_tree::split_iterator_i {
            replace_all_split& m_owner;
            eq_tree::node&     m_n;
            unsigned           m_idx;
            unsigned           m_next_case = 1;
        public:
            iterator(replace_all_split& owner, eq_tree::node& n, unsigned idx) : m_owner(owner), m_n(n), m_idx(idx) {}
            bool next(eq_tree::edge& out) override;
        };

        bool apply_case(eq_tree::node& n, unsigned idx, unsigned c, eq_tree::edge& out);
    public:
        replace_all_split(ast_manager& m, seq_util& u) : m(m), u(u) {}
        // Whether case number c is within the admissible range
        // (1..2*pattern_length+1) for a pattern of the given length.
        // Computed in 64-bit arithmetic and exposed so the boundary can
        // be unit-tested directly, without constructing a multi-gigabyte
        // zstring to reach pattern lengths near 2^31 (where the naive
        // unsigned computation of 2*pattern_length+2 wraps).
        static bool case_in_range(uint64_t c, uint64_t pattern_length) {
            return c < 2 * pattern_length + 2;
        }
        char const* name() const override { return "replace-all-split"; }
        scoped_ptr<eq_tree::split_iterator_i> split(eq_tree::node& n, unsigned cost, eq_tree::edge& out, bool& has_more, bool& committed) override;
        void collect_statistics(::statistics& st) const override { st.update("seq-replace-all num splits", m_stats.m_num_splits); }
        void reset_statistics() override { m_stats.reset(); }
    };

}
