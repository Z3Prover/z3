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
#include "math/polysat/boolean.h"
#include "math/polysat/constraint.h"
#include "math/polysat/eq_constraint.h"
#include "math/polysat/var_constraint.h"
#include "math/polysat/ule_constraint.h"
#include "math/polysat/justification.h"
#include "math/polysat/linear_solver.h"
#include "math/polysat/search_state.h"
#include "math/polysat/trail.h"
#include "math/polysat/log.h"

namespace polysat {

    class solver {

        struct stats {
            unsigned m_num_decisions;
            unsigned m_num_propagations;
            unsigned m_num_conflicts;
            void reset() { memset(this, 0, sizeof(*this)); }
            stats() { reset(); }
        };

        friend class constraint;
        friend class eq_constraint;
        friend class var_constraint;
        friend class ule_constraint;
        friend class forbidden_intervals;
        friend class linear_solver;

        typedef ptr_vector<constraint> constraints;

        reslimit&                m_lim;
        linear_solver            m_linear_solver;
        scoped_ptr_vector<dd::pdd_manager> m_pdd;
        scoped_ptr_vector<dd::fdd> m_bits;
        dd::bdd_manager          m_bdd;
        dep_value_manager        m_value_manager;
        small_object_allocator   m_alloc;
        poly_dep_manager         m_dm;
        constraints_and_clauses  m_conflict;
        // constraints              m_stash_just;
        var_queue                m_free_vars;
        stats                    m_stats;

        uint64_t                 m_max_conflicts { std::numeric_limits<uint64_t>::max() };
        uint64_t                 m_max_decisions { std::numeric_limits<uint64_t>::max() };

        // Map boolean variables to constraints
        bool_var_manager         m_bvars;

        // Per constraint state
        constraint_manager       m_constraints;
        ptr_vector<constraint>   m_original;
        ptr_vector<constraint>   m_redundant;
        scoped_ptr_vector<clause>       m_redundant_clauses;

        svector<sat::bool_var>   m_disjunctive_lemma;

        // Per variable information
        vector<bdd>              m_viable;   // set of viable values.
        vector<rational>         m_value;    // assigned value
        vector<justification>    m_justification; // justification for variable assignment
        vector<constraints>      m_cjust;    // constraints justifying variable range.
        vector<constraints>      m_watch;    // watch list datastructure into constraints.
        unsigned_vector          m_activity; 
        vector<pdd>              m_vars;
        unsigned_vector          m_size;     // store size of variables.

        search_state             m_search;
        assignment_t const& assignment() const { return m_search.assignment(); }

        // (old, remove later)
        // using bool_clauses = ptr_vector<bool_clause>;
        // vector<lbool>            m_bool_value;   // value of boolean literal (indexed by literal)
        // vector<bool_clauses>     m_bool_watch;   // watch list into clauses (indexed by literal)
        // // scoped_ptr_vector<bool_clause>  m_bool_clauses;  // NOTE: as of now, external clauses will only be units! So this is not needed.
        // svector<sat::literal>        m_bool_units;   // externally asserted unit clauses, via assign_eh
        // scoped_ptr_vector<bool_clause>  m_bool_redundant;   // learned clause storage

        unsigned                 m_qhead { 0 }; // next item to propagate (index into m_search)
        unsigned                 m_level { 0 };

        svector<trail_instr_t>   m_trail;
        unsigned_vector          m_qhead_trail;
        vector<std::pair<pvar, bdd>> m_viable_trail;
        unsigned_vector          m_cjust_trail;
        ptr_vector<constraint>   m_activate_trail;


        unsigned_vector          m_base_levels;  // External clients can push/pop scope. 


        void push_viable(pvar v) {
            m_trail.push_back(trail_instr_t::viable_i);
            m_viable_trail.push_back(std::make_pair(v, m_viable[v]));
        }

        void push_qhead() { 
            m_trail.push_back(trail_instr_t::qhead_i);
            m_qhead_trail.push_back(m_qhead);
        }

        void pop_qhead() {
            m_qhead = m_qhead_trail.back();
            m_qhead_trail.pop_back();
        }

        void push_cjust(pvar v, constraint* c) {
            if (m_cjust[v].contains(c))  // TODO: better check (flag on constraint?)
                return;
            LOG_V("cjust[v" << v << "] += " << *c);
            m_cjust[v].push_back(c);        
            m_trail.push_back(trail_instr_t::just_i);
            m_cjust_trail.push_back(v);
        }

        unsigned size(pvar v) const { return m_size[v]; }

        /**
         * Check whether variable v has any viable values left according to m_viable.
         */
        bool has_viable(pvar v);

        /**
         * check if value is viable according to m_viable.
         */
        bool is_viable(pvar v, rational const& val);

        /**
         * register that val is non-viable for var.
         */
        void add_non_viable(pvar v, rational const& val);

        /**
         * Register all values that are not contained in vals as non-viable.
         */
        void intersect_viable(pvar v, bdd vals);

        /**
         * Add dependency for variable viable range.
         */
        void add_viable_dep(pvar v, p_dependency* dep);

        /**
         * Find a next viable value for variable.
         */
        dd::find_t find_viable(pvar v, rational & val);

        /** Log all viable values for the given variable.
         * (Inefficient, but useful for debugging small instances.)
         */
        void log_viable(pvar v);

        /**
         * undo trail operations for backtracking.
         * Each struct is a subclass of trail and implements undo().
         */

        void del_var();

        dd::pdd_manager& sz2pdd(unsigned sz);
        dd::fdd const& sz2bits(unsigned sz);
        dd::fdd const& var2bits(pvar v) { return sz2bits(size(v)); }

        void push_level();
        void pop_levels(unsigned num_levels);
        void pop_constraints(ptr_vector<constraint>& cs);

        void assign_bool_backtrackable(sat::literal lit, clause* reason, clause* lemma);
        void activate_constraint_base(constraint* c);
        void assign_bool_core(sat::literal lit, clause* reason, clause* lemma);
        // void assign_bool_base(sat::literal lit);
        void activate_constraint(constraint& c, bool is_true);
        void deactivate_constraint(constraint& c);
        void decide_bool(sat::literal lit, clause* lemma);
        void propagate_bool(sat::literal lit, clause* reason);

        void assign_core(pvar v, rational const& val, justification const& j);
        bool is_assigned(pvar v) const { return !m_justification[v].is_unassigned(); }


        bool should_search();

        void propagate(sat::literal lit);
        void propagate(pvar v);
        void propagate(pvar v, rational const& val, constraint& c);
        void erase_watch(pvar v, constraint& c);
        void erase_watch(constraint& c);
        void add_watch(constraint& c);
        void add_watch(constraint& c, pvar v);

        void set_conflict(constraint& c);
        void set_conflict(pvar v);

        unsigned_vector m_marks;
        unsigned        m_clock { 0 };
        void reset_marks();
        bool is_marked(pvar v) const { return m_clock == m_marks[v]; }
        void set_mark(pvar v) { m_marks[v] = m_clock; }

        void set_marks(constraints_and_clauses const& cc);
        void set_marks(constraint const& c);
        void set_marks(clause const& cl);

        unsigned                 m_conflict_level { 0 };

        scoped_clause resolve(pvar v);

        bool can_decide() const { return !m_free_vars.empty(); }
        void decide();
        void decide(pvar v);

        void narrow(pvar v);
        void linear_propagate();

        p_dependency* mk_dep(unsigned dep) { return dep == null_dependency ? nullptr : m_dm.mk_leaf(dep); }
        p_dependency_ref mk_dep_ref(unsigned dep) { return p_dependency_ref(mk_dep(dep), m_dm); }

        bool is_conflict() const { return !m_conflict.empty(); }
        bool at_base_level() const;
        unsigned base_level() const;

        void resolve_conflict();
        void resolve_conflict_clause(scoped_clause& lemma);
        void backtrack(unsigned i, scoped_clause& lemma);
        void report_unsat();
        void revert_decision(pvar v, scoped_clause& reason);
        void revert_bool_decision(sat::literal lit, scoped_clause& reason);
        void learn_lemma(pvar v, scoped_clause& cl);
        void backjump(unsigned new_level);
        void add_lemma(scoped_clause& lemma);

        scoped_ptr<constraint> mk_eq(pdd const& p, unsigned dep);
        scoped_ptr<constraint> mk_diseq(pdd const& p, unsigned dep);
        scoped_ptr<constraint> mk_ule(pdd const& p, pdd const& q, unsigned dep);
        scoped_ptr<constraint> mk_ult(pdd const& p, pdd const& q, unsigned dep);
        scoped_ptr<constraint> mk_sle(pdd const& p, pdd const& q, unsigned dep);
        scoped_ptr<constraint> mk_slt(pdd const& p, pdd const& q, unsigned dep);
        void new_constraint(scoped_ptr<constraint>&& c, bool activate);
        static void insert_constraint(ptr_vector<constraint>& cs, constraint* c);

        bool invariant();
        static bool invariant(ptr_vector<constraint> const& cs);
        bool wlist_invariant();

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
         * Return value of v in the current model (only meaningful if check_sat() returned l_true).
         */
        rational get_value(pvar v) const { SASSERT(!m_justification[v].is_unassigned()); return m_value[v]; }

        /**
         * Create polynomial constraints (but do not activate them).
         * Each constraint is tracked by a dependency.
         */
        void new_eq(pdd const& p, unsigned dep);
        void new_diseq(pdd const& p, unsigned dep);
        void new_ule(pdd const& p, pdd const& q, unsigned dep);
        void new_ult(pdd const& p, pdd const& q, unsigned dep);
        void new_sle(pdd const& p, pdd const& q, unsigned dep);
        void new_slt(pdd const& p, pdd const& q, unsigned dep);

        /** Create and activate polynomial constraints. */
        void add_eq(pdd const& p, unsigned dep = null_dependency);
        void add_diseq(pdd const& p, unsigned dep = null_dependency);
        void add_ule(pdd const& p, pdd const& q, unsigned dep = null_dependency);
        void add_ult(pdd const& p, pdd const& q, unsigned dep = null_dependency);
        void add_sle(pdd const& p, pdd const& q, unsigned dep = null_dependency);
        void add_slt(pdd const& p, pdd const& q, unsigned dep = null_dependency);
        
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

    };

    inline std::ostream& operator<<(std::ostream& out, solver const& s) { return s.display(out); }

}


