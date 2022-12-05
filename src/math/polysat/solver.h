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

#include "util/statistics.h"
#include "util/params.h"
#include "math/polysat/boolean.h"
#include "math/polysat/conflict.h"
#include "math/polysat/constraint.h"
#include "math/polysat/constraint_manager.h"
#include "math/polysat/clause_builder.h"
#include "math/polysat/simplify_clause.h"
#include "math/polysat/simplify.h"
#include "math/polysat/restart.h"
#include "math/polysat/ule_constraint.h"
#include "math/polysat/justification.h"
#include "math/polysat/linear_solver.h"
#include "math/polysat/search_state.h"
#include "math/polysat/assignment.h"
#include "math/polysat/trail.h"
#include "math/polysat/viable.h"
#include "math/polysat/log.h"
#include <limits>
#include <optional>

namespace polysat {

    struct config {
        uint64_t    m_max_conflicts = std::numeric_limits<uint64_t>::max();
        uint64_t    m_max_decisions = std::numeric_limits<uint64_t>::max();
        bool        m_log_conflicts = false;
    };

    /**
     * A metric to evaluate lemmas from conflict analysis.
     * Lower is better.
     *
     * Comparison criterion:
     * - Lowest jump level has priority, because otherwise, some of the accumulated lemmas may still be false after backjumping.
     * - To break ties on jump level, choose clause with the fewest literals at its highest decision level;
     *   to limit case splits.
     */
    class lemma_score {
        unsigned m_jump_level;
        unsigned m_literals_at_max_level;

    public:
        lemma_score(unsigned jump_level, unsigned at_max_level)
            : m_jump_level(jump_level), m_literals_at_max_level(at_max_level)
        { }

        unsigned jump_level() const { return m_jump_level; }
        unsigned literals_at_max_level() const { return m_literals_at_max_level; }

        static lemma_score max() {
            return {UINT_MAX, UINT_MAX};
        }

        bool operator==(lemma_score const& other) const {
            return m_jump_level == other.m_jump_level
                && m_literals_at_max_level == other.m_literals_at_max_level;
        }
        bool operator!=(lemma_score const& other) const { return !operator==(other); }

        bool operator<(lemma_score const& other) const {
            return m_jump_level < other.m_jump_level
                || (m_jump_level == other.m_jump_level && m_literals_at_max_level < other.m_literals_at_max_level);
        }
        bool operator>(lemma_score const& other) const { return other.operator<(*this); }
        bool operator<=(lemma_score const& other) const { return operator==(other) || operator<(other); }
        bool operator>=(lemma_score const& other) const { return operator==(other) || operator>(other); }

        std::ostream& display(std::ostream& out) const {
            return out << "jump_level=" << m_jump_level << " at_max_level=" << m_literals_at_max_level;
        }
    };

    inline std::ostream& operator<<(std::ostream& out, lemma_score const& ls) { return ls.display(out); }

    class solver {

        struct stats {
            unsigned m_num_iterations;
            unsigned m_num_decisions;
            unsigned m_num_propagations;
            unsigned m_num_conflicts;
            unsigned m_num_restarts;
            unsigned m_num_viable_fallback;  ///< how often did we query the univariate solver
            void reset() { memset(this, 0, sizeof(*this)); }
            stats() { reset(); }
        };

        friend class assignment;
        friend class constraint;
        friend class ule_constraint;
        friend class umul_ovfl_constraint;
        friend class smul_fl_constraint;
        friend class op_constraint;
        friend class signed_constraint;
        friend class clause;
        friend class clause_builder;
        friend class conflict;
        friend class conflict_explainer;
        friend class simplify_clause;
        friend class simplify;
        friend class restart;
        friend class explainer;
        friend class inference_engine;
        friend class file_inference_logger;
        friend class forbidden_intervals;
        friend class linear_solver;
        friend class viable;
        friend class viable_fallback;
        friend class search_state;
        friend class num_pp;
        friend class lit_pp;
        friend class assignment_pp;
        friend class assignments_pp;
        friend class ex_polynomial_superposition;
        friend class free_variable_elimination;
        friend class saturation;
        friend class constraint_manager;
        friend class scoped_solverv;
        friend class test_polysat;
        friend class test_fi;
        friend struct inf_resolve_with_assignment;

        reslimit&                m_lim;
        params_ref               m_params;

        mutable scoped_ptr_vector<dd::pdd_manager> m_pdd;
        viable                   m_viable;   // viable sets per variable
        viable_fallback          m_viable_fallback;   // fallback for viable, using bitblasting over univariate constraints
        linear_solver            m_linear_solver;
        conflict                 m_conflict;
        simplify_clause          m_simplify_clause;
        simplify                 m_simplify;
        restart                  m_restart;
        bool_var_manager         m_bvars;       // Map boolean variables to constraints
        var_queue                m_free_pvars;  // free poly vars
        stats                    m_stats;

        config                   m_config;
        // Per constraint state
        constraint_manager       m_constraints;

        // Per variable information
        vector<rational>         m_value;         // assigned value
        vector<justification>    m_justification; // justification for variable assignment
        vector<constraints>      m_pwatch;        // watch list datastructure into constraints.
#ifndef NDEBUG
        std::optional<pvar>      m_locked_wlist;  // restrict watch list modification while it is being propagated
        bool                     m_is_propagating = false;  // set to true during propagation
        bool                     m_is_solving = false;  // set to true during solving
#endif

        unsigned_vector          m_activity;
        vector<pdd>              m_vars;
        unsigned_vector          m_size;     // store size of variables (bit width)

        search_state             m_search;

        unsigned                 m_qhead = 0; // next item to propagate (index into m_search)
        unsigned                 m_level = 0;

        svector<trail_instr_t>   m_trail;
        unsigned_vector          m_qhead_trail;
        constraints              m_pwatch_queue;
#if 0
        constraints              m_pwatch_trail;
#endif

        ptr_vector<clause>       m_lemmas;  ///< the non-asserting lemmas
        unsigned                 m_lemmas_qhead = 0;

        unsigned_vector          m_base_levels;  // External clients can push/pop scope.

        void push_qhead() {
            m_trail.push_back(trail_instr_t::qhead_i);
            m_qhead_trail.push_back(m_qhead);
        }

        void pop_qhead() {
            m_qhead = m_qhead_trail.back();
            m_qhead_trail.pop_back();
        }

        unsigned size(pvar v) const { return m_size[v]; }

        /**
         * undo trail operations for backtracking.
         * Each struct is a subclass of trail and implements undo().
         */

        void del_var();

        dd::pdd_manager& sz2pdd(unsigned sz) const;
        dd::pdd_manager& var2pdd(pvar v) const;

        assignment const& assignment() const { return m_search.assignment(); }

        void push_level();
        void pop_levels(unsigned num_levels);

        void try_assign_eval(signed_constraint c);

        void assign_propagate(sat::literal lit, clause& reason);
        void assign_decision(sat::literal lit);
        void assign_eval(sat::literal lit);
        void activate_constraint(signed_constraint c);
        unsigned level(sat::literal lit, clause const& cl);

        void assign_propagate(pvar v, rational const& val);
        void assign_verify(pvar v, rational val, justification j);
        void assign_core(pvar v, rational const& val, justification const& j);
        bool is_assigned(pvar v) const { return !m_justification[v].is_unassigned(); }
        bool is_decision(pvar v) const { return m_justification[v].is_decision(); }

        bool should_search();

        void propagate(sat::literal lit);
        void propagate(pvar v);
        bool propagate(pvar v, constraint* c);
        bool propagate(sat::literal lit, clause& cl);
        void enqueue_pwatch(constraint* c);
        bool should_add_pwatch() const;
        void add_pwatch();
        void add_pwatch(constraint* c);
        void add_pwatch(constraint* c, pvar v);
        void erase_pwatch(pvar v, constraint* c);
        void erase_pwatch(constraint* c);

        void set_conflict_at_base_level() { m_conflict.init_at_base_level(); }
        void set_conflict(signed_constraint c) { m_conflict.init(c); }
        void set_conflict(clause& cl) { m_conflict.init(cl); }
        void set_conflict(pvar v, bool by_viable_fallback) { m_conflict.init(v, by_viable_fallback); }

        bool can_decide() const;
        bool can_bdecide() const;
        bool can_pdecide() const;
        void decide();
        void bdecide();
        void pdecide(pvar v);

        void linear_propagate();

        bool is_conflict() const { return !m_conflict.empty(); }
        bool at_base_level() const;
        unsigned base_level() const;

        void resolve_conflict();
        void revert_decision(pvar v);
        void revert_bool_decision(sat::literal lit);
        void backjump_and_learn(unsigned jump_level, clause& lemma);
        void backjump_and_learn(unsigned max_jump_level);
        std::optional<lemma_score> compute_lemma_score(clause const& lemma);

        // activity of variables based on standard VSIDS
        unsigned m_activity_inc = 128;
        unsigned m_variable_decay = 110;
        void inc_activity(pvar v);
        void decay_activity();
        void rescale_activity();

        void report_unsat();
        void learn_lemma(clause& lemma);
        void backjump(unsigned new_level);

        void add_clause(clause& clause);
        void add_clause(signed_constraint c1, bool is_redundant);
        void add_clause(signed_constraint c1, signed_constraint c2, bool is_redundant);
        void add_clause(signed_constraint c1, signed_constraint c2, signed_constraint c3, bool is_redundant);
        void add_clause(signed_constraint c1, signed_constraint c2, signed_constraint c3, signed_constraint c4, bool is_redundant);
        void add_clause(std::initializer_list<signed_constraint> cs, bool is_redundant);
        void add_clause(unsigned n, signed_constraint const* cs, bool is_redundant);

        // Create a clause without adding it to the solver.
        clause_ref mk_clause(signed_constraint c1, bool is_redundant);
        clause_ref mk_clause(signed_constraint c1, signed_constraint c2, bool is_redundant);
        clause_ref mk_clause(signed_constraint c1, signed_constraint c2, signed_constraint c3, bool is_redundant);
        clause_ref mk_clause(signed_constraint c1, signed_constraint c2, signed_constraint c3, signed_constraint c4, bool is_redundant);
        clause_ref mk_clause(signed_constraint c1, signed_constraint c2, signed_constraint c3, signed_constraint c4, signed_constraint c5, bool is_redundant);
        clause_ref mk_clause(std::initializer_list<signed_constraint> cs, bool is_redundant);
        clause_ref mk_clause(unsigned n, signed_constraint const* cs, bool is_redundant);

        signed_constraint lit2cnstr(sat::literal lit) const { return m_constraints.lookup(lit); }

        bool inc() { return m_lim.inc(); }

        bool invariant();
        static bool invariant(signed_constraints const& cs);
        bool wlist_invariant();
        bool assignment_invariant();
        bool verify_sat();

        bool can_propagate();
        void propagate();

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
         */
        lbool check_sat();

        /**
         * retrieve unsat core dependencies
         */
        void unsat_core(dependency_vector& deps);

        /**
         * Return value / level of v in the current model (only meaningful if check_sat() returned l_true).
         */
        rational get_value(pvar v) const { SASSERT(is_assigned(v)); return m_value[v]; }

        unsigned get_level(pvar v) const { SASSERT(is_assigned(v)); return m_justification[v].level(); }

        /**
         * Evaluate term under the current assignment.
         */
        bool try_eval(pdd const& p, rational& out_value) const;

        /**
         * Add variable with bit-size.
         */
        pvar add_var(unsigned sz);

        /**
         * Create polynomial terms
         */
        pdd var(pvar v) { return m_vars[v]; }

        /**
        * Create terms for unsigned quot-rem
        *
        * Return tuple (quot, rem)
        *
        * The following properties are enforced:
        * b*quot + rem = a
        * ~ovfl(b*quot)
        * rem < b or b = 0
        */
        std::pair<pdd, pdd> quot_rem(pdd const& a, pdd const& b) { return m_constraints.quot_rem(a, b); }

        /** Create expression for the logical right shift of p by q. */
        pdd lshr(pdd const& p, pdd const& q) { return m_constraints.lshr(p, q); }

        /** Create expression for the logical left shift of p by q. */
        pdd shl(pdd const& p, pdd const& q) { return m_constraints.shl(p, q); }

        /** Create expression for the bit-wise negation of p. */
        pdd bnot(pdd const& p) { return m_constraints.bnot(p); }

        /** Create expression for bit-wise and of p, q. */
        pdd band(pdd const& p, pdd const& q) { return m_constraints.band(p, q); }

        /** Create expression for bit-wise or of p, q. */
        pdd bor(pdd const& p, pdd const& q) { return m_constraints.bor(p, q); }

        /** Create expression for bit-wise xor of p, q. */
        pdd bxor(pdd const& p, pdd const& q) { return m_constraints.bxor(p, q); }

        /** Create expression for bit-wise nand of p, q. */
        pdd bnand(pdd const& p, pdd const& q) { return m_constraints.bnand(p, q); }

        /** Create expression for bit-wise nor of p, q. */
        pdd bnor(pdd const& p, pdd const& q) { return m_constraints.bnor(p, q); }

        /**
         * Create polynomial constant.
         */
        pdd value(rational const& v, unsigned sz);

        /**
         * Apply current substitution to p.
         */
        pdd subst(pdd const& p) const;

        /** Create constraints */
        signed_constraint eq(pdd const& p) { return m_constraints.eq(p); }
        signed_constraint diseq(pdd const& p) { return ~m_constraints.eq(p); }
        signed_constraint eq(pdd const& p, pdd const& q) { return eq(p - q); }
        signed_constraint diseq(pdd const& p, pdd const& q) { return diseq(p - q); }
        signed_constraint eq(pdd const& p, rational const& q) { return eq(p - q); }
        signed_constraint eq(pdd const& p, unsigned q) { return eq(p - q); }
        signed_constraint odd(pdd const& p) { return ~even(p); }
        signed_constraint even(pdd const& p) { return parity(p, 1); }
        signed_constraint parity(pdd const& p, unsigned k) { return eq(p*rational::power_of_two(p.manager().power_of_2() - k)); }
        signed_constraint diseq(pdd const& p, rational const& q) { return diseq(p - q); }
        signed_constraint diseq(pdd const& p, unsigned q) { return diseq(p - q); }
        signed_constraint ule(pdd const& p, pdd const& q) { return m_constraints.ule(p, q); }
        signed_constraint ule(pdd const& p, rational const& q) { return ule(p, p.manager().mk_val(q)); }
        signed_constraint ule(rational const& p, pdd const& q) { return ule(q.manager().mk_val(p), q); }
        signed_constraint ule(pdd const& p, int n) { return ule(p, rational(n)); }
        signed_constraint ule(int n, pdd const& p) { return ule(rational(n), p); }
        signed_constraint uge(pdd const& p, pdd const& q) { return ule(q, p); }
        signed_constraint uge(pdd const& p, rational const& q) { return ule(q, p); }
        signed_constraint ult(pdd const& p, pdd const& q) { return m_constraints.ult(p, q); }
        signed_constraint ult(pdd const& p, rational const& q) { return ult(p, p.manager().mk_val(q)); }
        signed_constraint ult(rational const& p, pdd const& q) { return ult(q.manager().mk_val(p), q); }
        signed_constraint sle(pdd const& p, pdd const& q) { return m_constraints.sle(p, q); }
        signed_constraint slt(pdd const& p, pdd const& q) { return m_constraints.slt(p, q); }
        signed_constraint slt(pdd const& p, rational const& q) { return slt(p, p.manager().mk_val(q)); }
        signed_constraint slt(rational const& p, pdd const& q) { return slt(q.manager().mk_val(p), q); }
        signed_constraint slt(pdd const& p, int n) { return slt(p, rational(n)); }
        signed_constraint slt(int n, pdd const& p) { return slt(rational(n), p); }
        signed_constraint sgt(pdd const& p, pdd const& q) { return slt(q, p); }
        signed_constraint sgt(pdd const& p, int n) { return slt(n, p); }
        signed_constraint sgt(int n, pdd const& p) { return slt(p, n); }
        signed_constraint umul_ovfl(pdd const& p, pdd const& q) { return m_constraints.umul_ovfl(p, q); }
        signed_constraint umul_ovfl(rational const& p, pdd const& q) { return umul_ovfl(q.manager().mk_val(p), q); }
        signed_constraint smul_ovfl(pdd const& p, pdd const& q) { return m_constraints.smul_ovfl(p, q); }
        signed_constraint smul_udfl(pdd const& p, pdd const& q) { return m_constraints.smul_udfl(p, q); }
        signed_constraint bit(pdd const& p, unsigned i) { return m_constraints.bit(p, i); }

        /** Create and activate constraints */
        void add_eq(pdd const& p, dependency dep = null_dependency)                         { assign_eh(eq(p), dep); }
        void add_eq(pdd const& p, pdd const& q, dependency dep = null_dependency)           { assign_eh(eq(p, q), dep); }
        void add_eq(pdd const& p, rational const& q, dependency dep = null_dependency)      { assign_eh(eq(p, q), dep); }
        void add_eq(pdd const& p, unsigned q, dependency dep = null_dependency)             { assign_eh(eq(p, q), dep); }
        void add_diseq(pdd const& p, dependency dep = null_dependency)                      { assign_eh(diseq(p), dep); }
        void add_diseq(pdd const& p, pdd const& q, dependency dep = null_dependency)        { assign_eh(diseq(p, q), dep); }
        void add_diseq(pdd const& p, rational const& q, dependency dep = null_dependency)   { assign_eh(diseq(p, q), dep); }
        void add_diseq(pdd const& p, unsigned q, dependency dep = null_dependency)          { assign_eh(diseq(p, q), dep); }
        void add_ule(pdd const& p, pdd const& q, dependency dep = null_dependency)          { assign_eh(ule(p, q), dep); }
        void add_ult(pdd const& p, pdd const& q, dependency dep = null_dependency)          { assign_eh(ult(p, q), dep); }
        void add_sle(pdd const& p, pdd const& q, dependency dep = null_dependency)          { assign_eh(sle(p, q), dep); }
        void add_slt(pdd const& p, pdd const& q, dependency dep = null_dependency)          { assign_eh(slt(p, q), dep); }
        void add_umul_noovfl(pdd const& p, pdd const& q, dependency dep = null_dependency)  { assign_eh(~umul_ovfl(p, q), dep); }
        void add_umul_ovfl(pdd const& p, pdd const& q, dependency dep = null_dependency)    { assign_eh(umul_ovfl(p, q), dep); }

        void add_ule(pdd const& p, rational const& q, dependency dep = null_dependency)     { add_ule(p, p.manager().mk_val(q), dep); }
        void add_ule(rational const& p, pdd const& q, dependency dep = null_dependency)     { add_ule(q.manager().mk_val(p), q, dep); }
        void add_ule(pdd const& p, unsigned q, dependency dep = null_dependency)            { add_ule(p, rational(q), dep); }
        void add_ule(unsigned p, pdd const& q, dependency dep = null_dependency)            { add_ule(rational(p), q, dep); }
        void add_ult(pdd const& p, rational const& q, dependency dep = null_dependency)     { add_ult(p, p.manager().mk_val(q), dep); }
        void add_ult(rational const& p, pdd const& q, dependency dep = null_dependency)     { add_ult(q.manager().mk_val(p), q, dep); }
        void add_ult(pdd const& p, unsigned q, dependency dep = null_dependency)            { add_ult(p, rational(q), dep); }
        void add_ult(unsigned p, pdd const& q, dependency dep = null_dependency)            { add_ult(rational(p), q, dep); }
        void add_umul_noovfl(pdd const& p, rational const& q, dependency dep = null_dependency)  { add_umul_noovfl(p, p.manager().mk_val(q), dep); }
        void add_umul_noovfl(rational const& p, pdd const& q, dependency dep = null_dependency)  { add_umul_noovfl(q, p, dep); }
        void add_umul_noovfl(pdd const& p, unsigned q, dependency dep = null_dependency)         { add_umul_noovfl(p, rational(q), dep); }
        void add_umul_noovfl(unsigned p, pdd const& q, dependency dep = null_dependency)         { add_umul_noovfl(q, p, dep); }

        /**
         * Activate the constraint corresponding to the given boolean variable.
         * Note: to deactivate, use push/pop.
         */
        void assign_eh(signed_constraint c, dependency dep);

        /**
         * Unit propagation accessible over API.
         */
        lbool unit_propagate();

        /**
         * External context managment.
         * Adds so-called user-scope.
         */
        void push();
        void pop(unsigned num_scopes = 1);

        std::ostream& display(std::ostream& out) const;

        void collect_statistics(statistics& st) const;

        params_ref const & params() const { return m_params;  }

        void updt_params(params_ref const& p);

        config const& get_config() const { return m_config; }

    };  // class solver

    class assignments_pp {  // TODO: can probably remove this now.
        solver const& s;
    public:
        assignments_pp(solver const& s): s(s) {}
        std::ostream& display(std::ostream& out) const;
    };

    class assignment_pp {
        solver const& s;
        pvar var;
        rational const& val;
        bool with_justification;
    public:
        assignment_pp(solver const& s, pvar var, rational const& val, bool with_justification = false): s(s), var(var), val(val), with_justification(with_justification) {}
        std::ostream& display(std::ostream& out) const;
    };

    class lit_pp {
        solver const& s;
        sat::literal lit;
    public:
        lit_pp(solver const& s, signed_constraint c): s(s), lit(c ? c.blit() : sat::null_literal) {}
        lit_pp(solver const& s, sat::literal lit): s(s), lit(lit) {}
        std::ostream& display(std::ostream& out) const;
    };

    /** Format value 'val' as member of the domain of 'var' */
    class num_pp {
        solver const& s;
        pvar var;
        rational const& val;
    public:
        num_pp(solver const& s, pvar var, rational const& val): s(s), var(var), val(val) {}
        std::ostream& display(std::ostream& out) const;
    };

    inline std::ostream& operator<<(std::ostream& out, solver const& s) { return s.display(out); }

    inline std::ostream& operator<<(std::ostream& out, num_pp const& v) { return v.display(out); }

    inline std::ostream& operator<<(std::ostream& out, lit_pp const& l) { return l.display(out); }

    inline std::ostream& operator<<(std::ostream& out, assignment_pp const& p) { return p.display(out); }

    inline std::ostream& operator<<(std::ostream& out, assignments_pp const& a) { return a.display(out); }

}
