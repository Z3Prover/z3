/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat solver

Abstract:

    Polynomial solver for modular arithmetic.

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

--*/
#pragma once

#include <limits>
#include "util/statistics.h"
#include "util/params.h"
#include "math/polysat/boolean.h"
#include "math/polysat/conflict_core.h"
#include "math/polysat/constraint.h"
#include "math/polysat/clause_builder.h"
#include "math/polysat/eq_constraint.h"
#include "math/polysat/explain.h"
#include "math/polysat/ule_constraint.h"
#include "math/polysat/justification.h"
#include "math/polysat/linear_solver.h"
#include "math/polysat/search_state.h"
#include "math/polysat/trail.h"
#include "math/polysat/viable.h"
#include "math/polysat/log.h"

namespace polysat {

    class solver {

        struct stats {
            unsigned m_num_iterations;
            unsigned m_num_decisions;
            unsigned m_num_propagations;
            unsigned m_num_conflicts;
            unsigned m_num_bailouts;
            void reset() { memset(this, 0, sizeof(*this)); }
            stats() { reset(); }
        };

        friend class constraint;
        friend class eq_constraint;
        friend class var_constraint;
        friend class ule_constraint;
        friend class clause;
        friend class clause_builder;
        friend class conflict_core;
        friend class conflict_explainer;
        friend class explainer;
        friend class inference_engine;
        friend class forbidden_intervals;
        friend class linear_solver;
        friend class viable;
        friend class assignment_pp;
        friend class assignments_pp;
        friend class inf_saturate;

        typedef ptr_vector<constraint> constraints;
        typedef vector<signed_constraint> signed_constraints;

        reslimit&                m_lim;
        params_ref               m_params;
        viable                   m_viable;   // viable sets per variable
        scoped_ptr_vector<dd::pdd_manager> m_pdd;
        dep_value_manager        m_value_manager;
        small_object_allocator   m_alloc;
        poly_dep_manager         m_dm;
        linear_solver            m_linear_solver;
        conflict_core            m_conflict;
        // constraints              m_stash_just;
        var_queue                m_free_vars;
        stats                    m_stats;

        uint64_t                 m_max_conflicts { std::numeric_limits<uint64_t>::max() };
        uint64_t                 m_max_decisions { std::numeric_limits<uint64_t>::max() };

        // Map boolean variables to constraints
        bool_var_manager         m_bvars;

        // Per constraint state
        constraint_manager       m_constraints;
        signed_constraints       m_original;
        signed_constraints       m_redundant;
        ptr_vector<clause>       m_redundant_clauses;

        svector<sat::bool_var>   m_disjunctive_lemma;

        // Per variable information
        vector<rational>         m_value;    // assigned value
        vector<justification>    m_justification; // justification for variable assignment
        vector<signed_constraints> m_cjust;    // constraints justifying variable range.
        vector<signed_constraints> m_watch;    // watch list datastructure into constraints.
        unsigned_vector          m_activity; 
        vector<pdd>              m_vars;
        unsigned_vector          m_size;     // store size of variables.

        search_state             m_search;
        assignment_t const& assignment() const { return m_search.assignment(); }

        unsigned                 m_qhead = 0; // next item to propagate (index into m_search)
        unsigned                 m_level = 0;

        svector<trail_instr_t>   m_trail;
        unsigned_vector          m_qhead_trail;
        unsigned_vector          m_cjust_trail;

        unsigned_vector          m_base_levels;  // External clients can push/pop scope. 


        void push_viable(pvar v) {
            m_viable.push_viable(v);
        }

        void push_qhead() { 
            m_trail.push_back(trail_instr_t::qhead_i);
            m_qhead_trail.push_back(m_qhead);
        }

        void pop_qhead() {
            m_qhead = m_qhead_trail.back();
            m_qhead_trail.pop_back();
        }

        void push_cjust(pvar v, signed_constraint c) {
            if (m_cjust[v].contains(c))  // TODO: better check (flag on constraint?)
                return;
            LOG_V("cjust[v" << v << "] += " << c);
            SASSERT(c);
            m_cjust[v].push_back(c);
            m_trail.push_back(trail_instr_t::just_i);
            m_cjust_trail.push_back(v);
        }

        unsigned size(pvar v) const { return m_size[v]; }

        /**
         * undo trail operations for backtracking.
         * Each struct is a subclass of trail and implements undo().
         */

        void del_var();

        dd::pdd_manager& sz2pdd(unsigned sz);

        void push_level();
        void pop_levels(unsigned num_levels);
        void pop_constraints(signed_constraints& cs);

        void assign_bool(sat::literal lit, clause* reason, clause* lemma);
        void activate_constraint(signed_constraint c);
        void deactivate_constraint(signed_constraint c);
        sat::literal decide_bool(clause& lemma);
        void decide_bool(sat::literal lit, clause& lemma);
        void propagate_bool(sat::literal lit, clause* reason);

        void assign_core(pvar v, rational const& val, justification const& j);
        bool is_assigned(pvar v) const { return !m_justification[v].is_unassigned(); }
        bool is_decision(search_item const& item) const;


        bool should_search();

        void propagate(sat::literal lit);
        void propagate(pvar v);
        void propagate(pvar v, rational const& val, signed_constraint c);
        void erase_watch(pvar v, signed_constraint c);
        void erase_watch(signed_constraint c);
        void add_watch(signed_constraint c);
        void add_watch(signed_constraint c, pvar v);

        void set_conflict(signed_constraint c);
        void set_conflict(pvar v);

        unsigned_vector m_marks;
        unsigned        m_clock { 0 };
        void reset_marks();
        bool is_marked(pvar v) const { return m_clock == m_marks[v]; }
        void set_mark(pvar v) { LOG_V("Marking: v" << v); m_marks[v] = m_clock; }

        void set_marks(conflict_core const& cc);
        void set_marks(constraint const& c);

        bool can_decide() const { return !m_free_vars.empty(); }
        void decide();
        void decide(pvar v);

        void narrow(pvar v);
        void linear_propagate();

        p_dependency* mk_dep(unsigned dep) { return dep == null_dependency ? nullptr : m_dm.mk_leaf(dep); }
        p_dependency_ref mk_dep_ref(unsigned dep) { return p_dependency_ref(mk_dep(dep), m_dm); }

        /// Evaluate term under the current assignment.
        bool try_eval(pdd const& p, rational& out_value) const;

        bool is_conflict() const { return !m_conflict.empty(); }
        bool at_base_level() const;
        unsigned base_level() const;

        void resolve_conflict();
        void resolve_value(pvar v);
        void resolve_bool(sat::literal lit);
        void revert_decision(pvar v);
        void revert_bool_decision(sat::literal lit);

        void report_unsat();
        void learn_lemma(pvar v, clause_ref lemma);
        void backjump(unsigned new_level);
        void add_lemma(clause_ref lemma);

        signed_constraint mk_eq(pdd const& p);
        signed_constraint mk_diseq(pdd const& p);
        signed_constraint mk_ule(pdd const& p, pdd const& q);
        signed_constraint mk_ult(pdd const& p, pdd const& q);
        signed_constraint mk_sle(pdd const& p, pdd const& q);
        signed_constraint mk_slt(pdd const& p, pdd const& q);
        void new_constraint(signed_constraint c, unsigned dep, bool activate);
        static void insert_constraint(signed_constraints& cs, signed_constraint c);

        bool invariant();
        static bool invariant(signed_constraints const& cs);
        bool wlist_invariant();
        bool assignment_invariant();
        bool verify_sat();

    public:

        /**
         * to share chronology we pass an external trail stack.
         * every update to the solver is going to be retractable
         * by pushing an undo action on the trail stack.
         */
        solver(reslimit& lim);

        ~solver();

        /**
         * End-game satisfiability checker.
         *
         * Returns l_undef if the search cannot proceed.
         * Possible reasons:
         * - Resource limits are exhausted.
         * - A disjunctive lemma should be learned. The disjunction needs to be handled externally.
         */
        lbool check_sat();

        /**
         * Returns the disjunctive lemma that should be learned,
         * or an empty vector if check_sat() terminated for a different reason.
         */
        svector<sat::bool_var> get_lemma() { return m_disjunctive_lemma; }
        bool pending_disjunctive_lemma() { return !m_disjunctive_lemma.empty(); }

        /**
         * retrieve unsat core dependencies
         */
        void unsat_core(unsigned_vector& deps);
        
        /**
         * Add variable with bit-size. 
         */
        pvar add_var(unsigned sz);

        /**
         * Create polynomial terms
         */
        pdd var(pvar v) { return m_vars[v]; }

        /**
         * Create polynomial constant.
         */
        pdd value(rational const& v, unsigned sz);

        /**
         * Return value of v in the current model (only meaningful if check_sat() returned l_true).
         */
        rational get_value(pvar v) const { SASSERT(!m_justification[v].is_unassigned()); return m_value[v]; }

        /**
         * Create polynomial constraints (but do not activate them).
         * Each constraint is tracked by a dependency.
         */
        void new_eq(pdd const& p, unsigned dep)                { new_constraint(mk_eq(p), dep, false); }
        void new_diseq(pdd const& p, unsigned dep)             { new_constraint(mk_diseq(p), dep, false); }
        void new_ule(pdd const& p, pdd const& q, unsigned dep) { new_constraint(mk_ule(p, q), dep, false); }
        void new_ult(pdd const& p, pdd const& q, unsigned dep) { new_constraint(mk_ult(p, q), dep, false); }
        void new_sle(pdd const& p, pdd const& q, unsigned dep) { new_constraint(mk_sle(p, q), dep, false); }
        void new_slt(pdd const& p, pdd const& q, unsigned dep) { new_constraint(mk_slt(p, q), dep, false); }

        /** Create and activate polynomial constraints. */
        void add_eq(pdd const& p, unsigned dep = null_dependency)                { new_constraint(mk_eq(p), dep, true); }
        void add_diseq(pdd const& p, unsigned dep = null_dependency)             { new_constraint(mk_diseq(p), dep, true); }
        void add_ule(pdd const& p, pdd const& q, unsigned dep = null_dependency) { new_constraint(mk_ule(p, q), dep, true); }
        void add_ult(pdd const& p, pdd const& q, unsigned dep = null_dependency) { new_constraint(mk_ult(p, q), dep, true); }
        void add_sle(pdd const& p, pdd const& q, unsigned dep = null_dependency) { new_constraint(mk_sle(p, q), dep, true); }
        void add_slt(pdd const& p, pdd const& q, unsigned dep = null_dependency) { new_constraint(mk_slt(p, q), dep, true); }
        
        /**
         * Activate the constraint corresponding to the given boolean variable.
         * Note: to deactivate, use push/pop.
         */
        void assign_eh(unsigned dep, bool is_true);

        /**
         * main state transitions.
         */
        bool can_propagate();
        void propagate();

        /**
         * External context managment.
         * Adds so-called user-scope.
         */
        void push();
        void pop(unsigned num_scopes = 1);
       
        std::ostream& display(std::ostream& out) const;

        void collect_statistics(statistics& st) const;

        params_ref& params() { return m_params;  }

    };

    class assignments_pp {
        solver const& s;
    public:
        assignments_pp(solver const& s): s(s) {}
        std::ostream& display(std::ostream& out) const;
    };

    class assignment_pp {
        solver const& s;
        pvar var;
        rational const& val;
    public:
        assignment_pp(solver const& s, pvar var, rational const& val): s(s), var(var), val(val) {}
        std::ostream& display(std::ostream& out) const;
    };

    inline std::ostream& operator<<(std::ostream& out, solver const& s) { return s.display(out); }

    inline std::ostream& operator<<(std::ostream& out, assignment_pp const& p) { return p.display(out); }

    inline std::ostream& operator<<(std::ostream& out, assignments_pp const& a) { return a.display(out); }

}


