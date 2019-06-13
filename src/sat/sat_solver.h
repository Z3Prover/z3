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
#ifndef SAT_SOLVER_H_
#define SAT_SOLVER_H_

#include <cmath>
#include "sat/sat_types.h"
#include "sat/sat_clause.h"
#include "sat/sat_watched.h"
#include "sat/sat_justification.h"
#include "sat/sat_var_queue.h"
#include "sat/sat_extension.h"
#include "sat/sat_config.h"
#include "sat/sat_cleaner.h"
#include "sat/sat_simplifier.h"
#include "sat/sat_scc.h"
#include "sat/sat_asymm_branch.h"
#include "sat/sat_iff3_finder.h"
#include "sat/sat_probing.h"
#include "sat/sat_mus.h"
#include "sat/sat_drat.h"
#include "sat/sat_parallel.h"
#include "sat/sat_local_search.h"
#include "sat/sat_solver_core.h"
#include "util/params.h"
#include "util/statistics.h"
#include "util/stopwatch.h"
#include "util/ema.h"
#include "util/trace.h"
#include "util/rlimit.h"
#include "util/scoped_ptr_vector.h"

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
        unsigned m_blocked_corr_sets;
        unsigned m_elim_var_res;
        unsigned m_elim_var_bdd;
        unsigned m_units;
        unsigned m_backtracks;
        unsigned m_backjumps;
        stats() { reset(); }
        void reset();
        void collect_statistics(statistics & st) const;
    };
    
    class solver : public solver_core {
    public:
        struct abort_solver {};
    protected:
        enum search_state { s_sat, s_unsat };

        bool                    m_checkpoint_enabled;
        config                  m_config;
        stats                   m_stats;
        scoped_ptr<extension>   m_ext;
        parallel*               m_par;
        drat                    m_drat;          // DRAT for generating proofs
        clause_allocator        m_cls_allocator[2];
        bool                    m_cls_allocator_idx;
        random_gen              m_rand;
        cleaner                 m_cleaner;
        model                   m_model;        
        model_converter         m_mc;
        bool                    m_model_is_current;
        simplifier              m_simplifier;
        scc                     m_scc;
        asymm_branch            m_asymm_branch;
        probing                 m_probing;
        mus                     m_mus;           // MUS for minimal core extraction
        bool                    m_inconsistent;
        bool                    m_searching;
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
        unsigned_vector         m_touched;
        unsigned                m_touch_index;
        literal_vector          m_replay_assign;
        // branch variable selection:
        svector<unsigned>       m_activity;
        unsigned                m_activity_inc;
        svector<uint64_t>       m_last_conflict;
        svector<uint64_t>       m_last_propagation;
        svector<uint64_t>       m_participated;
        svector<uint64_t>       m_canceled;
        svector<uint64_t>       m_reasoned;
        int                     m_action;
        double                  m_step_size;
        // phase
        svector<bool>           m_phase; 
        svector<bool>           m_best_phase;
        svector<bool>           m_prev_phase;
        svector<char>           m_assigned_since_gc;
        search_state            m_search_state; 
        unsigned                m_search_unsat_conflicts;
        unsigned                m_search_sat_conflicts;
        unsigned                m_search_next_toggle;
        unsigned                m_phase_counter; 
        unsigned                m_best_phase_size;
        unsigned                m_rephase_lim;
        unsigned                m_rephase_inc;
        var_queue               m_case_split_queue;
        unsigned                m_qhead;
        unsigned                m_scope_lvl;
        unsigned                m_search_lvl;
        ema                     m_fast_glue_avg;
        ema                     m_slow_glue_avg;
        ema                     m_fast_glue_backup;
        ema                     m_slow_glue_backup;
        ema                     m_trail_avg;
        literal_vector          m_trail;
        clause_wrapper_vector   m_clauses_to_reinit;
        std::string             m_reason_unknown;

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

        unsigned                m_par_id;        
        unsigned                m_par_limit_in;
        unsigned                m_par_limit_out;
        unsigned                m_par_num_vars;
        bool                    m_par_syncing_clauses;

        class lookahead*        m_cuber;
        class i_local_search*   m_local_search;

        statistics              m_aux_stats;

        void del_clauses(clause_vector& clauses);

        friend class integrity_checker;
        friend class cleaner;
        friend class simplifier;
        friend class scc;
        friend class big;
        friend class binspr;
        friend class elim_eqs;
        friend class asymm_branch;
        friend class probing;
        friend class iff3_finder;
        friend class mus;
        friend class drat;
        friend class ba_solver;
        friend class parallel;
        friend class lookahead;
        friend class local_search;
        friend class ddfw;
        friend class prob;
        friend class unit_walk;
        friend struct mk_stat;
        friend class elim_vars;
        friend class scoped_detach;
    public:
        solver(params_ref const & p, reslimit& l);
        ~solver() override;

        // -----------------------
        //
        // Misc
        //
        // -----------------------
        void updt_params(params_ref const & p) override;        
        static void collect_param_descrs(param_descrs & d);

        void collect_statistics(statistics & st) const override;
        void reset_statistics();
        void display_status(std::ostream & out) const override;
        
        /**
           \brief Copy (non learned) clauses from src to this solver.
           Create missing variables if needed.
           
           \pre the model converter of src and this must be empty
        */
        void copy(solver const & src, bool copy_learned = false);
        
        // -----------------------
        //
        // Variable & Clause creation
        //
        // -----------------------
        void add_clause(unsigned num_lits, literal * lits, bool learned) override { mk_clause(num_lits, lits, learned); }
        bool_var add_var(bool ext) override { return mk_var(ext, true); }

        bool_var mk_var(bool ext = false, bool dvar = true);
        clause* mk_clause(literal_vector const& lits, bool learned = false) { return mk_clause(lits.size(), lits.c_ptr(), learned); }
        clause* mk_clause(unsigned num_lits, literal * lits, bool learned = false);
        clause* mk_clause(literal l1, literal l2, bool learned = false);
        clause* mk_clause(literal l1, literal l2, literal l3, bool learned = false);        

        random_gen& rand() { return m_rand; }

    protected:
        inline clause_allocator& cls_allocator() { return m_cls_allocator[m_cls_allocator_idx]; }
        inline clause_allocator const& cls_allocator() const { return m_cls_allocator[m_cls_allocator_idx]; }
        inline clause * alloc_clause(unsigned num_lits, literal const * lits, bool learned) { return cls_allocator().mk_clause(num_lits, lits, learned); }
        inline void     dealloc_clause(clause* c) { cls_allocator().del_clause(c); }
        struct cmp_activity;
        void defrag_clauses();
        bool should_defrag();
        bool memory_pressure();
        void del_clause(clause & c);
        clause * mk_clause_core(unsigned num_lits, literal * lits, bool learned);
        clause * mk_clause_core(literal_vector const& lits) { return mk_clause_core(lits.size(), lits.c_ptr()); }
        clause * mk_clause_core(unsigned num_lits, literal * lits) { return mk_clause_core(num_lits, lits, false); }
        void mk_clause_core(literal l1, literal l2) { literal lits[2] = { l1, l2 }; mk_clause_core(2, lits); }
        void mk_bin_clause(literal l1, literal l2, bool learned);
        bool propagate_bin_clause(literal l1, literal l2);
        clause * mk_ter_clause(literal * lits, bool learned);
        bool attach_ter_clause(clause & c);
        clause * mk_nary_clause(unsigned num_lits, literal * lits, bool learned);
        bool attach_nary_clause(clause & c);
        void attach_clause(clause & c, bool & reinit);
        void attach_clause(clause & c) { bool reinit; attach_clause(c, reinit); }
        void set_learned(clause& c, bool learned);
        void shrink(clause& c, unsigned old_sz, unsigned new_sz);
        void set_learned(literal l1, literal l2, bool learned);
        void set_learned1(literal l1, literal l2, bool learned);
        void add_ate(clause& c) { m_mc.add_ate(c); }        
        void add_ate(literal l1, literal l2) { m_mc.add_ate(l1, l2); }        
        void add_ate(literal_vector const& lits) { m_mc.add_ate(lits); }

        class scoped_disable_checkpoint {
            solver& s;
        public:
            scoped_disable_checkpoint(solver& s): s(s) {
                s.m_checkpoint_enabled = false;
            }            
            ~scoped_disable_checkpoint() {
                s.m_checkpoint_enabled = true;
            }
        };
        unsigned select_watch_lit(clause const & cls, unsigned starting_at) const;
        unsigned select_learned_watch_lit(clause const & cls) const;
        bool simplify_clause(unsigned & num_lits, literal * lits) const;
        template<bool lvl0>
        bool simplify_clause_core(unsigned & num_lits, literal * lits) const;
        void detach_bin_clause(literal l1, literal l2, bool learned);
        void detach_clause(clause & c);
        void detach_nary_clause(clause & c);
        void detach_ter_clause(clause & c);
        void push_reinit_stack(clause & c);

        // -----------------------
        //
        // Basic
        //
        // -----------------------
    public:
        bool inconsistent() const override { return m_inconsistent; }
        unsigned num_vars() const override { return m_justification.size(); }
        unsigned num_clauses() const override;
        void num_binary(unsigned& given, unsigned& learned) const;
        unsigned num_restarts() const { return m_restarts; }
        bool is_external(bool_var v) const override { return m_external[v] != 0; }
        void set_external(bool_var v) override;
        void set_non_external(bool_var v) override;
        bool was_eliminated(bool_var v) const { return m_eliminated[v] != 0; }
        void set_eliminated(bool_var v, bool f) override;
        bool was_eliminated(literal l) const { return was_eliminated(l.var()); }
        unsigned scope_lvl() const { return m_scope_lvl; }
        unsigned search_lvl() const { return m_search_lvl; }
        bool  at_search_lvl() const { return m_scope_lvl == m_search_lvl; }
        bool  at_base_lvl() const override { return m_scope_lvl == 0; }
        lbool value(literal l) const { return static_cast<lbool>(m_assignment[l.index()]); }
        lbool value(bool_var v) const { return static_cast<lbool>(m_assignment[literal(v, false).index()]); }
        unsigned lvl(bool_var v) const { return m_justification[v].level(); }
        unsigned lvl(literal l) const { return m_justification[l.var()].level(); }
        unsigned init_trail_size() const override { return at_base_lvl() ? m_trail.size() : m_scopes[0].m_trail_lim; }
        unsigned trail_size() const { return m_trail.size(); }
        literal  trail_literal(unsigned i) const override { return m_trail[i]; }
        literal  scope_literal(unsigned n) const { return m_trail[m_scopes[n].m_trail_lim]; }
        void assign(literal l, justification j) {
            TRACE("sat_assign", tout << l << " previous value: " << value(l) << " j: " << j << "\n";);
            switch (value(l)) {
            case l_false: set_conflict(j, ~l); break;
            case l_undef: assign_core(l, j); break;
            case l_true:  return;
            }
        }
        void assign_unit(literal l) { assign(l, justification(0)); }
        void assign_scoped(literal l) { assign(l, justification(scope_lvl())); }
        void assign_core(literal l, justification jst);
        void set_conflict(justification c, literal not_l);
        void set_conflict(justification c) { set_conflict(c, null_literal); }
        void set_conflict() { set_conflict(justification(0)); }
        lbool status(clause const & c) const;        
        clause_offset get_offset(clause const & c) const { return cls_allocator().get_offset(&c); }

        bool limit_reached() {
            if (!m_rlimit.inc()) {
                m_mc.reset();
                m_model_is_current = false;
                TRACE("sat", tout << "canceled\n";);
                m_reason_unknown = "sat.canceled";
                return true;
            }
            return false;
        }

        bool memory_exceeded() {
            ++m_num_checkpoints;
            if (m_num_checkpoints < 10) return false;
            m_num_checkpoints = 0;
            return memory::get_allocation_size() > m_config.m_max_memory;
        }
        
        void checkpoint() {
            if (!m_checkpoint_enabled) return;
            if (limit_reached()) {
                throw solver_exception(Z3_CANCELED_MSG);
            }
            if (memory_exceeded()) {
                throw solver_exception(Z3_MAX_MEMORY_MSG);                
            }
        }
        void set_par(parallel* p, unsigned id);
        bool canceled() { return !m_rlimit.inc(); }
        config const& get_config() const { return m_config; }
        void set_incremental(bool b) { m_config.m_incremental = b; }
        bool is_incremental() const { return m_config.m_incremental; }
        extension* get_extension() const override { return m_ext.get(); }
        void       set_extension(extension* e) override;
        bool       set_root(literal l, literal r);
        void       flush_roots();
        typedef std::pair<literal, literal> bin_clause;
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
        bool should_propagate() const;
        bool propagate_core(bool update);
        
        // -----------------------
        //
        // Search
        //
        // -----------------------
    public:
        lbool check(unsigned num_lits = 0, literal const* lits = nullptr) override;

        model const & get_model() const override { return m_model; }
        bool model_is_current() const { return m_model_is_current; }
        literal_vector const& get_core() const override { return m_core; }
        model_converter const & get_model_converter() const { return m_mc; }
        void flush(model_converter& mc) override { mc.flush(m_mc); }
        void set_model(model const& mdl);
        char const* get_reason_unknown() const override { return m_reason_unknown.c_str(); }
        bool check_clauses(model const& m) const;
        bool is_assumption(bool_var v) const;
        void set_activity(bool_var v, unsigned act);

        lbool  cube(bool_var_vector& vars, literal_vector& lits, unsigned backtrack_level);
        
        void display_lookahead_scores(std::ostream& out);

    protected:

        unsigned m_conflicts_since_init;
        unsigned m_restarts;
        unsigned m_restart_next_out;
        unsigned m_conflicts_since_restart;
        bool     m_force_conflict_analysis;
        unsigned m_simplifications;
        unsigned m_restart_threshold;
        unsigned m_luby_idx;
        unsigned m_conflicts_since_gc;
        unsigned m_gc_threshold;
        unsigned m_defrag_threshold;
        unsigned m_num_checkpoints;
        double   m_min_d_tk;
        unsigned m_next_simplify;
        bool decide();
        bool_var next_var();
        lbool bounded_search();
        lbool final_check();
        lbool propagate_and_backjump_step(bool& done);
        void init_search();
        
        literal_vector m_min_core;
        bool           m_min_core_valid;
        void init_reason_unknown() { m_reason_unknown = "no reason given"; }
        void init_assumptions(unsigned num_lits, literal const* lits);
        void reassert_min_core();
        void update_min_core();
        void resolve_weighted();
        void reset_assumptions();
        void add_assumption(literal lit);
        void pop_assumption();
        void reinit_assumptions();
        bool tracking_assumptions() const;
        bool is_assumption(literal l) const;
        bool should_simplify() const;
        void do_simplify();
        void mk_model();
        bool check_model(model const & m) const;
        void do_restart(bool to_base);
        svector<size_t> m_last_positions;
        unsigned m_last_position_log;
        unsigned m_restart_logs;
        unsigned restart_level(bool to_base);
        void log_stats();
        bool should_cancel();
        bool should_restart() const;
        void set_next_restart();
        void update_activity(bool_var v, double p);
        bool reached_max_conflicts();
        void sort_watch_lits();
        void exchange_par();
        lbool check_par(unsigned num_lits, literal const* lits);
        lbool do_local_search(unsigned num_lits, literal const* lits);
        lbool do_ddfw_search(unsigned num_lits, literal const* lits);
        lbool do_prob_search(unsigned num_lits, literal const* lits);
        lbool invoke_local_search(unsigned num_lits, literal const* lits);
        lbool do_unit_walk();

        // -----------------------
        //
        // GC
        //
        // -----------------------
    protected:
        bool should_gc() const;
        void do_gc();
        void gc_glue();
        void gc_psm();
        void gc_glue_psm();
        void gc_psm_glue();
        void save_psm();
        void gc_half(char const * st_name);
        void gc_dyn_psm();
        bool activate_frozen_clause(clause & c);
        unsigned psm(clause const & c) const;
        bool can_delete(clause const & c) const;
        bool can_delete3(literal l1, literal l2, literal l3) const;

        clause& get_clause(watch_list::iterator it) const {
            SASSERT(it->get_kind() == watched::CLAUSE);
            return get_clause(it->get_clause_offset());
        }

        clause& get_clause(watched const& w) const {
            SASSERT(w.get_kind() == watched::CLAUSE);
            return get_clause(w.get_clause_offset());
        }

        clause& get_clause(justification const& j) const {
            SASSERT(j.is_clause());
            return get_clause(j.get_clause_offset());
        }

        clause& get_clause(clause_offset cls_off) const {
            return *(cls_allocator().get_clause(cls_off));
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
        bool use_backjumping(unsigned num_scopes);
        bool resolve_conflict();
        lbool resolve_conflict_core();
        void learn_lemma_and_backjump();
        inline unsigned update_max_level(literal lit, unsigned lvl2, bool& unique_max) {
            unsigned lvl1 = lvl(lit);
            if (lvl1 < lvl2) return lvl2;
            unique_max = lvl1 > lvl2;
            return lvl1;
        }
        unsigned get_max_lvl(literal consequent, justification js, bool& unique_max);
        void process_antecedent(literal antecedent, unsigned & num_marks);
        void resolve_conflict_for_unsat_core();
        void process_antecedent_for_unsat_core(literal antecedent);
        void process_consequent_for_unsat_core(literal consequent, justification const& js);
        void fill_ext_antecedents(literal consequent, justification js);
        unsigned skip_literals_above_conflict_level();
        void updt_phase_of_vars();
        void updt_phase_counters();
        void do_toggle_search_state();
        bool should_toggle_search_state();
        bool is_sat_phase() const;
        bool is_two_phase() const;
        bool should_rephase();
        void do_rephase();
        svector<char> m_diff_levels;
        unsigned num_diff_levels(unsigned num, literal const * lits);
        bool     num_diff_levels_below(unsigned num, literal const* lits, unsigned max_glue, unsigned& glue);
        bool     num_diff_false_levels_below(unsigned num, literal const* lits, unsigned max_glue, unsigned& glue);

        // lemma minimization
        typedef approx_set_tpl<unsigned, u2u, unsigned> level_approx_set;
        bool_var_vector   m_unmark;
        level_approx_set  m_lvl_set;
        literal_vector    m_lemma_min_stack;
        bool process_antecedent_for_minimization(literal antecedent);
        bool implied_by_marked(literal lit);
        void reset_unmark(unsigned old_size);
        void updt_lemma_lvl_set();
        bool minimize_lemma();
        bool minimize_lemma_binres();
        void reset_lemma_var_marks();
        bool dyn_sub_res();

        // -----------------------
        //
        // Backtracking
        //
        // -----------------------
        void push();
        void pop(unsigned num_scopes);
        void pop_reinit(unsigned num_scopes);

        void unassign_vars(unsigned old_sz, unsigned new_lvl);
        void reinit_clauses(unsigned old_sz);

        literal_vector m_user_scope_literals;
        literal_vector m_aux_literals;
        svector<bin_clause> m_user_bin_clauses;
        void gc_lit(clause_vector& clauses, literal lit);
        void gc_bin(literal lit);
        void gc_var(bool_var v);

        bool_var max_var(clause_vector& clauses, bool_var v);
        bool_var max_var(bool learned, bool_var v);

    public:
        void user_push() override;
        void user_pop(unsigned num_scopes) override;
        void pop_to_base_level() override;
        unsigned num_user_scopes() const override { return m_user_scope_literals.size(); }
        reslimit& rlimit() { return m_rlimit; }
        // -----------------------
        //
        // Simplification
        //
        // -----------------------
    public:
        bool do_cleanup(bool force);
        void simplify(bool learned = true);
        void asymmetric_branching();
        unsigned scc_bin();

        // -----------------------
        //
        // Auxiliary methods.
        //
        // -----------------------
    public:
        lbool find_mutexes(literal_vector const& lits, vector<literal_vector> & mutexes);

        lbool get_consequences(literal_vector const& assms, bool_var_vector const& vars, vector<literal_vector>& conseq);

        // initialize and retrieve local search.
        // local_search& init_local_search();

    private:

        typedef hashtable<unsigned, u_hash, u_eq> index_set;

        u_map<index_set>       m_antecedents;
        literal_vector         m_todo_antecedents;
        vector<literal_vector> m_binary_clause_graph;

        bool extract_assumptions(literal lit, index_set& s);
        
        bool check_domain(literal lit, literal lit2);

        std::ostream& display_index_set(std::ostream& out, index_set const& s) const;

        lbool get_consequences(literal_vector const& assms, literal_vector const& lits, vector<literal_vector>& conseq);

        lbool get_bounded_consequences(literal_vector const& assms, bool_var_vector const& vars, vector<literal_vector>& conseq);

        void delete_unfixed(literal_set& unfixed_lits, bool_var_set& unfixed_vars);

        void extract_fixed_consequences(unsigned& start, literal_set const& assumptions, bool_var_set& unfixed, vector<literal_vector>& conseq);

        void extract_fixed_consequences(literal_set const& unfixed_lits, literal_set const& assumptions, bool_var_set& unfixed, vector<literal_vector>& conseq);

        void extract_fixed_consequences(literal lit, literal_set const& assumptions, bool_var_set& unfixed, vector<literal_vector>& conseq);

        bool extract_fixed_consequences1(literal lit, literal_set const& assumptions, bool_var_set& unfixed, vector<literal_vector>& conseq);

        void update_unfixed_literals(literal_set& unfixed_lits, bool_var_set& unfixed_vars);

        void fixup_consequence_core();

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
            m_activity_inc *= m_config.m_variable_decay;
            m_activity_inc /= 100;
        }

    private:
        void rescale_activity();

        void update_chb_activity(bool is_sat, unsigned qhead);

        void update_lrb_reasoned();

        void update_lrb_reasoned(literal lit);

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
        clause_vector const& learned() const { return m_learned; }
        clause_vector const& clauses() const override { return m_clauses; }
        void collect_bin_clauses(svector<bin_clause> & r, bool learned, bool learned_only) const override;


        // -----------------------
        //
        // Debugging
        //
        // -----------------------
    public:
        bool check_invariant() const override;
        void display(std::ostream & out) const;
        void display_watches(std::ostream & out) const;
        void display_watches(std::ostream & out, literal lit) const;
        void display_dimacs(std::ostream & out) const override;
        std::ostream& display_model(std::ostream& out) const;
        void display_wcnf(std::ostream & out, unsigned sz, literal const* lits, unsigned const* weights) const;
        void display_assignment(std::ostream & out) const;
        std::ostream& display_justification(std::ostream & out, justification const& j) const;
        std::ostream& display_watch_list(std::ostream& out, watch_list const& wl) const;

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

    class scoped_detach {
        solver& s;
        clause& c;
        bool m_deleted;
    public:
        scoped_detach(solver& s, clause& c): s(s), c(c), m_deleted(false) {
            if (!c.frozen()) s.detach_clause(c);
        }            
        ~scoped_detach() {
            if (!m_deleted && !c.frozen()) s.attach_clause(c);
        }
        
        void del_clause() {
            if (!m_deleted) {
                s.del_clause(c);
                m_deleted = true;
            }
        }
    };


    std::ostream & operator<<(std::ostream & out, mk_stat const & stat);
};

#endif
