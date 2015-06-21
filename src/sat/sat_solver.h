/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    sat_solver.h

Abstract:

    SAT solver main class.

Author:

    Leonardo de Moura (leonardo) 2011-05-21.

Revision History:

--*/
#ifndef _SAT_SOLVER_H_
#define _SAT_SOLVER_H_

#include"sat_types.h"
#include"sat_clause.h"
#include"sat_watched.h"
#include"sat_justification.h"
#include"sat_var_queue.h"
#include"sat_extension.h"
#include"sat_config.h"
#include"sat_cleaner.h"
#include"sat_simplifier.h"
#include"sat_scc.h"
#include"sat_asymm_branch.h"
#include"sat_iff3_finder.h"
#include"sat_probing.h"
#include"sat_mus.h"
#include"sat_sls.h"
#include"params.h"
#include"statistics.h"
#include"stopwatch.h"
#include"trace.h"

namespace sat {

    /**
       \brief Main statistic counters.
    */
    struct stats {
        unsigned m_mk_var;
        unsigned m_mk_bin_clause;
        unsigned m_mk_ter_clause;
        unsigned m_mk_clause;
        unsigned m_conflict;
        unsigned m_propagate;
        unsigned m_bin_propagate;
        unsigned m_ter_propagate;
        unsigned m_decision;
        unsigned m_restart;
        unsigned m_gc_clause;
        unsigned m_del_clause;
        unsigned m_minimized_lits;
        unsigned m_dyn_sub_res;
        unsigned m_non_learned_generation;
        stats() { reset(); }
        void reset();
        void collect_statistics(statistics & st) const;
    };
    
    class solver {
    public:
        struct abort_solver {};
    protected:
        volatile bool           m_cancel;
        config                  m_config;
        stats                   m_stats;
        extension *             m_ext;
        random_gen              m_rand;
        clause_allocator        m_cls_allocator;
        cleaner                 m_cleaner;
        model                   m_model;        
        model_converter         m_mc;
        bool                    m_model_is_current;
        simplifier              m_simplifier;
        scc                     m_scc;
        asymm_branch            m_asymm_branch;
        probing                 m_probing;
        mus                     m_mus;           // MUS for minimal core extraction
        wsls                    m_wsls;          // SLS facility for MaxSAT use
        bool                    m_inconsistent;
        // A conflict is usually a single justification. That is, a justification
        // for false. If m_not_l is not null_literal, then m_conflict is a
        // justification for l, and the conflict is union of m_no_l and m_conflict;
        justification           m_conflict;
        literal                 m_not_l;
        clause_vector           m_clauses;
        clause_vector           m_learned;
        unsigned                m_num_frozen;
        vector<watch_list>      m_watches;
        char_vector             m_assignment;
        svector<justification>  m_justification; 
        svector<char>           m_decision;
        svector<char>           m_mark;
        svector<char>           m_lit_mark;
        svector<char>           m_eliminated;
        svector<char>           m_external;
        svector<unsigned>       m_level; 
        svector<unsigned>       m_activity;
        unsigned                m_activity_inc;
        svector<char>           m_phase; 
        svector<char>           m_prev_phase;
        svector<char>           m_assigned_since_gc;
        bool                    m_phase_cache_on;
        unsigned                m_phase_counter; 
        var_queue               m_case_split_queue;
        unsigned                m_qhead;
        unsigned                m_scope_lvl;
        literal_vector          m_trail;
        clause_wrapper_vector   m_clauses_to_reinit;
        struct scope {
            unsigned m_trail_lim;
            unsigned m_clauses_to_reinit_lim;
            bool     m_inconsistent;
        };
        svector<scope>          m_scopes;
        stopwatch               m_stopwatch;
        params_ref              m_params;
        scoped_ptr<solver>      m_clone; // for debugging purposes
        literal_vector          m_assumptions;      // additional assumptions during check
        literal_set             m_assumption_set;   // set of enabled assumptions
        literal_vector          m_core;             // unsat core

        void del_clauses(clause * const * begin, clause * const * end);

        friend class integrity_checker;
        friend class cleaner;
        friend class simplifier;
        friend class scc;
        friend class elim_eqs;
        friend class asymm_branch;
        friend class probing;
        friend class iff3_finder;
        friend class mus;
        friend class sls;
        friend class wsls;
        friend class bceq;
        friend struct mk_stat;
    public:
        solver(params_ref const & p, extension * ext);
        ~solver();

        // -----------------------
        //
        // Misc
        //
        // -----------------------
        void updt_params(params_ref const & p);
        static void collect_param_descrs(param_descrs & d);

        void set_cancel(bool f);
        void collect_statistics(statistics & st) const;
        void reset_statistics();
        void display_status(std::ostream & out) const;
        
        /**
           \brief Copy (non learned) clauses from src to this solver.
           Create missing variables if needed.
           
           \pre the model converter of src and this must be empty
        */
        void copy(solver const & src);
        
        // -----------------------
        //
        // Variable & Clause creation
        //
        // -----------------------
        bool_var mk_var(bool ext = false, bool dvar = true);
        void mk_clause(unsigned num_lits, literal * lits);
        void mk_clause(literal l1, literal l2);
        void mk_clause(literal l1, literal l2, literal l3);

    protected:
        void del_clause(clause & c);
        clause * mk_clause_core(unsigned num_lits, literal * lits, bool learned);
        void mk_bin_clause(literal l1, literal l2, bool learned);
        bool propagate_bin_clause(literal l1, literal l2);
        clause * mk_ter_clause(literal * lits, bool learned);
        void attach_ter_clause(clause & c, bool & reinit);
        void attach_ter_clause(clause & c) { bool reinit; attach_ter_clause(c, reinit); }
        clause * mk_nary_clause(unsigned num_lits, literal * lits, bool learned);
        void attach_nary_clause(clause & c, bool & reinit);
        void attach_nary_clause(clause & c) { bool reinit; attach_nary_clause(c, reinit); }
        void attach_clause(clause & c, bool & reinit);
        void attach_clause(clause & c) { bool reinit; attach_clause(c, reinit); }
        unsigned select_watch_lit(clause const & cls, unsigned starting_at) const;
        unsigned select_learned_watch_lit(clause const & cls) const;
        bool simplify_clause(unsigned & num_lits, literal * lits) const;
        template<bool lvl0>
        bool simplify_clause_core(unsigned & num_lits, literal * lits) const;
        void dettach_bin_clause(literal l1, literal l2, bool learned);
        void dettach_clause(clause & c);
        void dettach_nary_clause(clause & c);
        void dettach_ter_clause(clause & c);
        void push_reinit_stack(clause & c);

        // -----------------------
        //
        // Basic
        //
        // -----------------------
    public:
        bool inconsistent() const { return m_inconsistent; }
        unsigned num_vars() const { return m_level.size(); }
        unsigned num_clauses() const;
        bool is_external(bool_var v) const { return m_external[v] != 0; }
        bool was_eliminated(bool_var v) const { return m_eliminated[v] != 0; }
        unsigned scope_lvl() const { return m_scope_lvl; }
        lbool value(literal l) const { return static_cast<lbool>(m_assignment[l.index()]); }
        lbool value(bool_var v) const { return static_cast<lbool>(m_assignment[literal(v, false).index()]); }
        unsigned lvl(bool_var v) const { return m_level[v]; }
        unsigned lvl(literal l) const { return m_level[l.var()]; }
        void assign(literal l, justification j) {
            TRACE("sat_assign", tout << l << " previous value: " << value(l) << "\n";);
            switch (value(l)) {
            case l_false: set_conflict(j, ~l); break;
            case l_undef: assign_core(l, j); break;
            case l_true:  return;
            }
        }
        void assign_core(literal l, justification jst);
        void set_conflict(justification c, literal not_l);
        void set_conflict(justification c) { set_conflict(c, null_literal); }
        lbool status(clause const & c) const;        
        clause_offset get_offset(clause const & c) const { return m_cls_allocator.get_offset(&c); }
        void checkpoint() {
            if (m_cancel) throw solver_exception(Z3_CANCELED_MSG);
            ++m_num_checkpoints;
            if (m_num_checkpoints < 10) return;
            m_num_checkpoints = 0;
            if (memory::get_allocation_size() > m_config.m_max_memory) throw solver_exception(Z3_MAX_MEMORY_MSG);
        }
        typedef std::pair<literal, literal> bin_clause;
        void initialize_soft(unsigned sz, literal const* lits, double const* weights);
    protected:
        watch_list & get_wlist(literal l) { return m_watches[l.index()]; }
        watch_list const & get_wlist(literal l) const { return m_watches[l.index()]; }
        watch_list & get_wlist(unsigned l_idx) { return m_watches[l_idx]; }
        bool is_marked(bool_var v) const { return m_mark[v] != 0; }
        void mark(bool_var v) { SASSERT(!is_marked(v)); m_mark[v] = true; }
        void reset_mark(bool_var v) { SASSERT(is_marked(v)); m_mark[v] = false; }
        bool is_marked_lit(literal l) const { return m_lit_mark[l.index()] != 0; }
        void mark_lit(literal l) { SASSERT(!is_marked_lit(l)); m_lit_mark[l.index()] = true; }
        void unmark_lit(literal l) { SASSERT(is_marked_lit(l)); m_lit_mark[l.index()] = false; }
        bool check_inconsistent();


        // -----------------------
        //
        // Propagation
        //
        // -----------------------
    public:
        // if update == true, then glue of learned clauses is updated.
        bool propagate(bool update);

    protected:
        bool propagate_core(bool update);
        
        // -----------------------
        //
        // Search
        //
        // -----------------------
    public:
        lbool check(unsigned num_lits = 0, literal const* lits = 0);
        model const & get_model() const { return m_model; }
        bool model_is_current() const { return m_model_is_current; }
        literal_vector const& get_core() const { return m_core; }
        model_converter const & get_model_converter() const { return m_mc; }

    protected:
        unsigned m_conflicts;
        unsigned m_conflicts_since_restart;
        unsigned m_restart_threshold;
        unsigned m_luby_idx;
        unsigned m_conflicts_since_gc;
        unsigned m_gc_threshold;
        unsigned m_num_checkpoints;
        double   m_min_d_tk;
        unsigned m_next_simplify;
        bool decide();
        bool_var next_var();
        lbool bounded_search();
        void init_search();
        void init_assumptions(unsigned num_lits, literal const* lits);
        void reinit_assumptions();
        bool tracking_assumptions() const;
        bool is_assumption(literal l) const;
        void simplify_problem();
        void mk_model();
        bool check_model(model const & m) const;
        void restart();
        void sort_watch_lits();

        // -----------------------
        //
        // GC
        //
        // -----------------------
    protected:
        void gc();
        void gc_glue();
        void gc_psm();
        void gc_glue_psm();
        void gc_psm_glue();
        void save_psm();
        void gc_half(char const * st_name);
        void gc_dyn_psm();
        bool activate_frozen_clause(clause & c);
        unsigned psm(clause const & c) const;
        bool can_delete(clause const & c) const {
            if (c.on_reinit_stack())
                return false;
            if (c.size() == 3)
                return true; // not needed to justify anything.
            literal l0 = c[0];
            if (value(l0) != l_true)
                return true;
            justification const & jst = m_justification[l0.var()];
            return !jst.is_clause() || m_cls_allocator.get_clause(jst.get_clause_offset()) != &c;
        }
        
        // -----------------------
        //
        // Conflict resolution
        //
        // -----------------------
    protected:
        unsigned       m_conflict_lvl;
        literal_vector m_lemma;
        literal_vector m_ext_antecedents;
        bool resolve_conflict();
        bool resolve_conflict_core();
        void resolve_conflict_for_unsat_core();
        unsigned get_max_lvl(literal consequent, justification js);
        void process_antecedent(literal antecedent, unsigned & num_marks);
        void process_antecedent_for_unsat_core(literal antecedent);
        void process_consequent_for_unsat_core(literal consequent, justification const& js);
        void fill_ext_antecedents(literal consequent, justification js);
        unsigned skip_literals_above_conflict_level();
        void forget_phase_of_vars(unsigned from_lvl);
        void updt_phase_counters();
        svector<char> m_diff_levels;
        unsigned num_diff_levels(unsigned num, literal const * lits);

        // lemma minimization
        typedef approx_set_tpl<unsigned, u2u, unsigned> level_approx_set;
        bool_var_vector   m_unmark;
        level_approx_set  m_lvl_set;
        bool_var_vector   m_lemma_min_stack;
        bool process_antecedent_for_minimization(literal antecedent);
        bool implied_by_marked(literal lit);
        void reset_unmark(unsigned old_size);
        void updt_lemma_lvl_set();
        void minimize_lemma();
        void reset_lemma_var_marks();
        void dyn_sub_res();

        // -----------------------
        //
        // Backtracking
        //
        // -----------------------
        void push();
        void pop(unsigned num_scopes);
        void pop_reinit(unsigned num_scopes);

        void unassign_vars(unsigned old_sz);
        void reinit_clauses(unsigned old_sz);

        literal_vector m_user_scope_literals;
        literal_vector m_user_scope_literal_pool;
        literal_vector m_aux_literals;
        svector<bin_clause> m_user_bin_clauses;
        void gc_lit(clause_vector& clauses, literal lit);
        void gc_bin(bool learned, literal nlit);
    public:
        void user_push();
        void user_pop(unsigned num_scopes);
        void pop_to_base_level();
        // -----------------------
        //
        // Simplification
        //
        // -----------------------
    public:
        void cleanup();
        void simplify(bool learned = true);
        void asymmetric_branching();
        unsigned scc_bin();

        // -----------------------
        //
        // Activity related stuff
        //
        // -----------------------
    public:
        void inc_activity(bool_var v) {
            unsigned & act = m_activity[v];
            act += m_activity_inc;
            m_case_split_queue.activity_increased_eh(v);
            if (act > (1 << 24))
                rescale_activity();
        }

        void decay_activity() {
            m_activity_inc *= 11;
            m_activity_inc /= 10;
        }

    private:
        void rescale_activity();

        // -----------------------
        //
        // Iterators
        //
        // -----------------------
    public:
        clause * const * begin_clauses() const { return m_clauses.begin(); }
        clause * const * end_clauses() const { return m_clauses.end(); }
        clause * const * begin_learned() const { return m_learned.begin(); }
        clause * const * end_learned() const { return m_learned.end(); }
        void collect_bin_clauses(svector<bin_clause> & r, bool learned) const;

        // -----------------------
        //
        // Debugging
        //
        // -----------------------
    public:
        bool check_invariant() const;
        void display(std::ostream & out) const;
        void display_watches(std::ostream & out) const;
        void display_dimacs(std::ostream & out) const;
        void display_assignment(std::ostream & out) const;
        void display_justification(std::ostream & out, justification const& j) const;

    protected:
        void display_binary(std::ostream & out) const;
        void display_units(std::ostream & out) const;
        bool is_unit(clause const & c) const;
        bool is_empty(clause const & c) const;
        bool check_missed_propagation(clause_vector const & cs) const;
        bool check_missed_propagation() const;
        bool check_marks() const;
    };
    
    struct mk_stat {
        solver const & m_solver;
        mk_stat(solver const & s):m_solver(s) {}
        void display(std::ostream & out) const;
    };

    std::ostream & operator<<(std::ostream & out, mk_stat const & stat);
};

#endif
