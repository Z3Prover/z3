/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_solver_facet.h

Abstract:

    Arithmetic facet for the search tree.

    `solver_facet` delegates integer constraints, primarily sequence
    lengths derived from `eq_facet`, to a shared incremental SMT solver.
    The backend is pushed and popped in sync with DFS backtracking. The
    facet currently generates length equalities and basic non-negativity
    facts; `unknown` is treated conservatively as unresolved.

Author:

    Nikolaj Bjorner (nbjorner) 2026
    Clemens Eisenhofer 2026
    Margus Veanes 2026

--*/
#pragma once

#include "ast/ast.h"
#include "model/model.h"
#include "ast/seq_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/seq/seq_eq_facet.h"
#include "ast/seq/seq_sub_solver.h"
#include "ast/seq/seq_solver_facet_i.h"
#include "util/stx_search_tree.h"
#include "util/trail.h"
#include "util/params.h"
#include "util/obj_hashtable.h"

class solver;

namespace seq {

    /**
     * `sub_solver_i` backed by one shared `solver`.
     * Dependency-tracked assertions use assumption literals so UNSAT
     * cores can be mapped back to `dep_tracker`s. Literal slots are
     * reused across push/pop scopes.
     */
    class sub_solver : public sub_solver_i {
        ast_manager&              m;
        solver*                   m_solver; // owned
        expr_ref_vector           m_assump_lits;   // assumption exprs; reused, only grows
        obj_map<expr, unsigned>   m_assump_lit2id; // assumption expr -> its slot index
        svector<unsigned>         m_frame_bounds;  // m_deps.size() at each push()
        vector<eq_tree::dep_tracker> m_deps;       // slot id -> dep
        eq_tree::dep_manager_t&   m_core_dep_mgr;
        eq_tree::dep_tracker      m_last_core = nullptr;
        bool                      m_dirty = true;  // assertions changed since the last check()
        lbool                     m_last_result = l_undef;
        model_ref                 m_model;         // of the last check(), fetched lazily

    public:
        sub_solver(ast_manager& m, arith_util& a, eq_tree::dep_manager_t& core_dep_mgr);
        ~sub_solver() override;

        void assert_expr(expr* e, eq_tree::dep_tracker dep = nullptr) override;
        void push() override;
        void pop(unsigned n) override;
        unsigned get_scope_level() const override;
        lbool check() override;
        eq_tree::dep_tracker unsat_core() const override { return m_last_core; }
        bool get_model(model_ref& md) override;
    };

    /**
     * Holds the arithmetic constraints added at this node only.
     * Child nodes clone their parent state structurally, so `m_own`
     * contains exactly the constraints that must be pushed when the node
     * is entered and popped when it is left.
     */
    class solver_facet : public solver_facet_i {
        ast_manager&      m;
        arith_util        a;
        seq_util&         u;
        sub_solver_i&     m_solver;
        expr_ref_vector   m_own;       // constraints added at this node only
        unsigned          m_pushed_at_scope = 0; // trail scope level at which the backend scope currently in effect was pushed (0 = none pushed yet)
        model_ref         m_model;                       // arithmetic model captured by clone() at a sat leaf

        // Pairs the backend push for a trail scope with the matching pop.
        class scope_trail : public ::trail {
            sub_solver_i& m_solver;
            unsigned&     m_pushed_at_scope;
            unsigned      m_old_value;
        public:
            explicit scope_trail(sub_solver_i& s, unsigned& pushed_at_scope) :
                m_solver(s), m_pushed_at_scope(pushed_at_scope), m_old_value(pushed_at_scope) { s.push(); }
            void undo() override { m_solver.pop(1); m_pushed_at_scope = m_old_value; }
        };

        // Undo object for expr_ref_vector::push_back().
        class push_back_ref_trail : public ::trail {
            expr_ref_vector& m_vec;
        public:
            explicit push_back_ref_trail(expr_ref_vector& v) : m_vec(v) {}
            void undo() override { m_vec.pop_back(); }
        };

    public:
        solver_facet(trail_stack& trail, ast_manager& m, seq_util& u, sub_solver_i& solver) :
            solver_facet_i(trail), m(m), a(m), u(u), m_solver(solver), m_own(m) {}

        ast_manager& get_manager() const { return m; }
        arith_util& get_arith_util() override { return a; }
        seq_util& get_seq_util() const { return u; }

        // Add one branch-local arithmetic constraint. The first add at a
        // trail scope lazily opens a matching backend scope. `dep`, when
        // present, is forwarded so UNSAT cores can explain the conflict.
        // Returns false if the constraint was already recorded.
        bool add_constraint(expr* c, eq_tree::dep_tracker dep = nullptr) override;

        // Add `len(lhs) = len(rhs)` and `len(v) >= 0` facts for any
        // sequence variables encountered. Returns true iff something new
        // was recorded.
        bool add_length_constraint(expr_ref_vector const& lhs, expr_ref_vector const& rhs, eq_tree::dep_tracker dep = nullptr) override;

        // -- stx::facet_i --
        stx::facet_i* clone(trail_stack& trail) const override;
        // A node is satisfied only when the arithmetic backend says `sat`.
        bool is_satisfied() const override { return m_solver.check() == l_true; }

        bool has_conflict() const override { return m_solver.check() == l_false; }

        // Dependency explaining the current conflict, if any. It may be
        // `nullptr` when the conflict only uses unconditional facts.
        eq_tree::dep_tracker conflict_dep() const override { return m_solver.unsat_core(); }

        // Probe whether `c` is implied without permanently asserting it.
        lbool implies(expr* c, eq_tree::dep_tracker* core = nullptr) const override;
        bool value(expr* e, rational& v) const override;
        std::ostream& display(std::ostream& out) const override;
    };


    // Deterministic propagation from eq_facet into solver_facet.
    class arith_propagation : public eq_tree::propagation_plugin_i {
        ast_manager&  m;
        seq_util&     u;
        struct stats {
            unsigned m_num_propagate = 0;
            void reset() { *this = stats(); }
        };
        stats m_stats;
    public:
        arith_propagation(ast_manager& m, seq_util& u) :
            m(m), u(u) {}
        char const* name() const override { return "arith-propagate"; }
        stx::simplify_result propagate(eq_tree::node& n) override;
        void collect_statistics(::statistics& st) const override { st.update("seq-arith-propagate num calls", m_stats.m_num_propagate); }
        void reset_statistics() override { m_stats.reset(); }
    };

} // namespace seq
