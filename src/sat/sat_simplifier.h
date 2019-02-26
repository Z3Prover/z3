/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    sat_simplifier.h

Abstract:

    SAT simplification procedures that use a "full" occurrence list:
    Subsumption, Blocked Clause Removal, Variable Elimination, ...


Author:

    Leonardo de Moura (leonardo) 2011-05-24.

Revision History:

--*/
#ifndef SAT_SIMPLIFIER_H_
#define SAT_SIMPLIFIER_H_

#include "sat/sat_types.h"
#include "sat/sat_clause.h"
#include "sat/sat_clause_set.h"
#include "sat/sat_clause_use_list.h"
#include "sat/sat_extension.h"
#include "sat/sat_watched.h"
#include "sat/sat_model_converter.h"
#include "util/heap.h"
#include "util/statistics.h"
#include "util/params.h"

namespace sat {
    class solver;

    class use_list {
        vector<clause_use_list> m_use_list;
    public:
        void init(unsigned num_vars);
        void insert(clause & c);
        void block(clause & c);
        void unblock(clause & c);
        void erase(clause & c);
        void erase(clause & c, literal l);
        clause_use_list & get(literal l) { return m_use_list[l.index()]; }
        clause_use_list const & get(literal l) const { return m_use_list[l.index()]; }
        void finalize() { m_use_list.finalize(); }
        std::ostream& display(std::ostream& out, literal l) const { return m_use_list[l.index()].display(out); }
    };

    class simplifier {
        friend class ba_solver;
        friend class elim_vars;
        solver &               s;
        unsigned               m_num_calls;
        use_list               m_use_list;
        ext_use_list           m_ext_use_list;
        clause_set             m_sub_todo;
        svector<bin_clause>    m_sub_bin_todo;
        unsigned               m_last_sub_trail_sz; // size of the trail since last cleanup
        bool_var_set           m_elim_todo;
        bool                   m_need_cleanup;
        tmp_clause             m_dummy;

        // simplifier extra variable fields.
        svector<char>          m_visited; // transient

        // counters
        int                    m_sub_counter;
        int                    m_elim_counter;

        // config
        bool                   m_abce; // block clauses using asymmetric added literals
        bool                   m_cce;  // covered clause elimination
        bool                   m_acce; // cce with asymmetric literal addition
        bool                   m_bca;  // blocked (binary) clause addition. 
        unsigned               m_bce_delay; 
        bool                   m_bce;  // blocked clause elimination
        bool                   m_ate;  // asymmetric tautology elimination
        unsigned               m_bce_at;
        bool                   m_retain_blocked_clauses;
        unsigned               m_blocked_clause_limit;
        bool                   m_incremental_mode; 
        bool                   m_resolution;
        unsigned               m_res_limit;
        unsigned               m_res_occ_cutoff;
        unsigned               m_res_occ_cutoff1;
        unsigned               m_res_occ_cutoff2;
        unsigned               m_res_occ_cutoff3;
        unsigned               m_res_lit_cutoff1;
        unsigned               m_res_lit_cutoff2;
        unsigned               m_res_lit_cutoff3;
        unsigned               m_res_cls_cutoff1;
        unsigned               m_res_cls_cutoff2;

        bool                   m_subsumption;
        unsigned               m_subsumption_limit;
        bool                   m_elim_vars;
        bool                   m_elim_vars_bdd;
        unsigned               m_elim_vars_bdd_delay;

        // stats
        unsigned               m_num_bce;
        unsigned               m_num_cce;
        unsigned               m_num_acce;
        unsigned               m_num_abce;
        unsigned               m_num_bca;
        unsigned               m_num_ate;
        unsigned               m_num_subsumed;
        unsigned               m_num_elim_vars;
        unsigned               m_num_sub_res;
        unsigned               m_num_elim_lits;

        bool                   m_learned_in_use_lists;
        unsigned               m_old_num_elim_vars;

        struct size_lt {
            bool operator()(clause const * c1, clause const * c2) const { return c1->size() > c2->size(); }
        };

        void checkpoint();

        void initialize();

        void init_visited();
        void mark_visited(literal l) { m_visited[l.index()] = true; }
        void unmark_visited(literal l) { m_visited[l.index()] = false; }
        bool is_marked(literal l) const { return m_visited[l.index()] != 0; }
        void mark_all_but(clause const & c, literal l);
        void unmark_all(clause const & c);

        void register_clauses(clause_vector & cs);

        void remove_clause(clause & c, bool is_unique);
        void set_learned(clause & c);
        void set_learned(literal l1, literal l2);

        bool_var get_min_occ_var(clause const & c) const;
        bool subsumes1(clause const & c1, clause const & c2, literal & l);
        void collect_subsumed1_core(clause const & c, clause_vector & out, literal_vector & out_lits, literal target);
        void collect_subsumed1(clause const & c, clause_vector & out, literal_vector & out_lits);
        clause_vector  m_bs_cs;
        literal_vector m_bs_ls;
        void back_subsumption1(clause & c);
        void back_subsumption1(literal l1, literal l2, bool learned);

        literal get_min_occ_var0(clause const & c) const;
        bool subsumes0(clause const & c1, clause const & c2);
        void collect_subsumed0_core(clause const & c1, clause_vector & out, literal target);
        void collect_subsumed0(clause const & c1, clause_vector & out);
        void back_subsumption0(clause & c1);

        bool cleanup_clause(clause & c);
        bool cleanup_clause(literal_vector & c);
        void elim_lit(clause & c, literal l);
        void elim_dup_bins();
        bool subsume_with_binaries();
        void mark_as_not_learned_core(watch_list & wlist, literal l2);
        void mark_as_not_learned(literal l1, literal l2);

        void cleanup_watches();
        void move_clauses(clause_vector & cs, bool learned);
        void cleanup_clauses(clause_vector & cs, bool learned, bool vars_eliminated);

        bool is_external(bool_var v) const;
        bool is_external(literal l) const { return is_external(l.var()); }
        bool was_eliminated(bool_var v) const;
        lbool value(bool_var v) const;
        lbool value(literal l) const;
        watch_list & get_wlist(literal l);
        watch_list const & get_wlist(literal l) const;

        struct blocked_clause_elim;
        void elim_blocked_clauses();

        bool single_threaded() const; // { return s.m_config.m_num_threads == 1; }
        bool bce_enabled_base() const;
        bool ate_enabled()  const;
        bool bce_enabled()  const;
        bool acce_enabled() const;
        bool cce_enabled()  const;
        bool abce_enabled() const;
        bool bca_enabled()  const;
        bool elim_vars_bdd_enabled() const;
        bool elim_vars_enabled() const;

        unsigned num_nonlearned_bin(literal l) const;
        unsigned get_to_elim_cost(bool_var v) const;
        void order_vars_for_elim(bool_var_vector & r);
        void collect_clauses(literal l, clause_wrapper_vector & r);
        clause_wrapper_vector m_pos_cls;
        clause_wrapper_vector m_neg_cls;
        literal_vector m_new_cls;
        bool resolve(clause_wrapper const & c1, clause_wrapper const & c2, literal l, literal_vector & r);
        void save_clauses(model_converter::entry & mc_entry, clause_wrapper_vector const & cs);
        void add_non_learned_binary_clause(literal l1, literal l2);
        void remove_bin_clauses(literal l);
        void remove_clauses(clause_use_list const & cs, literal l);
        bool try_eliminate(bool_var v);
        void elim_vars();

        struct blocked_cls_report;
        struct subsumption_report;
        struct elim_var_report;

        class scoped_finalize {
            simplifier& s;
        public:
            scoped_finalize(simplifier& s) : s(s) {}
            ~scoped_finalize() { s.scoped_finalize_fn(); }
        };
        void scoped_finalize_fn();

    public:
        simplifier(solver & s, params_ref const & p);
        ~simplifier();

        void init_search() { m_num_calls = 0; }

        void insert_elim_todo(bool_var v) { m_elim_todo.insert(v); }

        void reset_todos() {
            m_elim_todo.reset();
            m_sub_todo.reset();
            m_sub_bin_todo.reset();
        }

        void operator()(bool learned);

        void updt_params(params_ref const & p);
        static void collect_param_descrs(param_descrs & d);

        void finalize();

        void collect_statistics(statistics & st) const;
        void reset_statistics();

        void propagate_unit(literal l);
        void subsume();

    };
};

#endif
