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

#include"sat_types.h"
#include"sat_clause.h"
#include"sat_clause_set.h"
#include"sat_clause_use_list.h"
#include"sat_watched.h"
#include"sat_model_converter.h"
#include"heap.h"
#include"statistics.h"
#include"params.h"

namespace sat {
    class solver;

    class use_list {
        vector<clause_use_list> m_use_list;
    public:
        void init(unsigned num_vars);
        void insert(clause & c);
        void erase(clause & c);
        void erase(clause & c, literal l);
        clause_use_list & get(literal l) { return m_use_list[l.index()]; }
        clause_use_list const & get(literal l) const { return m_use_list[l.index()]; }
        void finalize() { m_use_list.finalize(); }
    };

    class simplifier {
        solver &               s;
        unsigned               m_num_calls;
        use_list               m_use_list;
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
        bool                   m_elim_blocked_clauses;
        unsigned               m_elim_blocked_clauses_at;
        unsigned               m_blocked_clause_limit;
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
        
        // stats
        unsigned               m_num_blocked_clauses;
        unsigned               m_num_subsumed;
        unsigned               m_num_elim_vars;
        unsigned               m_num_sub_res;
        unsigned               m_num_elim_lits;

        struct size_lt {
            bool operator()(clause const * c1, clause const * c2) const { return c1->size() > c2->size(); }
        };

        void checkpoint();

        void init_visited();
        void mark_visited(literal l) { m_visited[l.index()] = true; }
        void unmark_visited(literal l) { m_visited[l.index()] = false; }
        bool is_marked(literal l) const { return m_visited[l.index()] != 0; }
        void mark_all_but(clause const & c, literal l);
        void unmark_all(clause const & c);

        void register_clauses(clause_vector & cs);

        void remove_clause_core(clause & c);
        void remove_clause(clause & c);
        void remove_clause(clause & c, literal l);
        void remove_bin_clause_half(literal l1, literal l2, bool learned);

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

        bool cleanup_clause(clause & c, bool in_use_list);
        bool cleanup_clause(literal_vector & c);
        void propagate_unit(literal l);
        void elim_lit(clause & c, literal l);
        void elim_dup_bins();
        bool subsume_with_binaries();
        void mark_as_not_learned_core(watch_list & wlist, literal l2);
        void mark_as_not_learned(literal l1, literal l2);
        void subsume();
        
        void cleanup_watches();
        void cleanup_clauses(clause_vector & cs, bool learned, bool vars_eliminated, bool in_use_lists);

        bool is_external(bool_var v) const;
        bool was_eliminated(bool_var v) const;
        lbool value(bool_var v) const;
        lbool value(literal l) const;
        watch_list & get_wlist(literal l);
        watch_list const & get_wlist(literal l) const;
        
        struct blocked_clause_elim;
        void elim_blocked_clauses();

        unsigned get_num_non_learned_bin(literal l) const;
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

    public:
        simplifier(solver & s, params_ref const & p);
        ~simplifier();

        void insert_todo(bool_var v) { m_elim_todo.insert(v); }
        void reset_todo() { m_elim_todo.reset(); }

        void operator()(bool learned);

        void updt_params(params_ref const & p);
        static void collect_param_descrs(param_descrs & d);
        
        void free_memory();

        void collect_statistics(statistics & st) const;
        void reset_statistics();
    };
};

#endif
