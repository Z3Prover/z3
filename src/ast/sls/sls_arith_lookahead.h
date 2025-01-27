/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    sls_arith_lookahead

Abstract:

    Theory plugin for arithmetic local search 
    based on lookahead search as used in HybridSMT

Author:

    Nikolaj Bjorner (nbjorner) 2025-01-16

--*/
#pragma once

#include "util/checked_int64.h"
#include "util/optional.h"
#include "util/nat_set.h"
#include "ast/ast_trail.h"
#include "ast/arith_decl_plugin.h"
#include "ast/sls/sls_context.h"


namespace sls {
    
    template<typename num_t>
    class arith_base;

    using var_t = unsigned;

    enum arith_move_type {
        hillclimb,
        hillclimb_plateau,
        random_update,
        random_inc_dec
    };

    std::ostream& operator<<(std::ostream& out, arith_move_type mt);

    template<typename num_t>
    class arith_lookahead {
        context& ctx;
        ast_manager& m;
        class arith_base<num_t>& a;
        arith_util autil;

        struct bool_info {
            unsigned weight = 0;
            double   score = 0;
            unsigned touched = 1;
            lbool    value = l_undef;
            sat::bool_var_vector fixable_atoms;
            svector<var_t>       fixable_vars;
            ptr_vector<expr>     fixable_exprs;
            bool_info(unsigned w) : weight(w) {}
        };

        vector<ptr_vector<app>> m_update_stack;
        expr_mark m_in_update_stack;
        scoped_ptr_vector<bool_info> m_bool_info;
        double m_best_score = 0, m_top_score = 0;
        unsigned m_min_depth = 0, m_max_depth = 0;
        num_t m_best_value;
        expr* m_best_expr = nullptr, * m_last_atom = nullptr, * m_last_expr = nullptr;
        expr_mark m_is_root;
        unsigned m_touched = 1;
        sat::bool_var_set m_fixed_atoms;
        uint64_t m_tabu_set = 0;
        unsigned m_global_search_count = 0;

        bool in_tabu_set(expr* e, num_t const& n);
        void insert_tabu_set(expr* e, num_t const& n);
        bool_info& get_bool_info(expr* e);
        bool get_bool_value(expr* e);
        bool get_bool_value_rec(expr* e);
        void set_bool_value(expr* e, bool v) { get_bool_info(e).value = to_lbool(v); }
        bool get_basic_bool_value(app* e);
        double old_score(expr* e) { return get_bool_info(e).score; }
        double new_score(expr* e);
        double new_score(expr* e, bool is_true);
        void set_score(expr* e, double s) { get_bool_info(e).score = s; }
        void rescore();
        void recalibrate_weights();
        void inc_weight(expr* e) { ++get_bool_info(e).weight;  }
        void dec_weight(expr* e);
        unsigned get_weight(expr* e) { return get_bool_info(e).weight; }
        unsigned get_touched(expr* e) { return get_bool_info(e).touched; }
        void inc_touched(expr* e) { ++get_bool_info(e).touched; }
        void set_touched(expr* e, unsigned t) { get_bool_info(e).touched = t; }
        void insert_update_stack(expr* t);
        void insert_update_stack_rec(expr* t);
        void clear_update_stack();
        void lookahead_num(var_t v, num_t const& value);
        void lookahead_bool(expr* e);
        double lookahead(expr* e, bool update_score);
        void add_lookahead(bool_info& i, expr* e);
        void add_lookahead(bool_info& i, sat::bool_var bv);
        ptr_vector<expr> const& get_fixable_exprs(expr* e);
        bool apply_move(expr* f, ptr_vector<expr> const& vars, arith_move_type t);
        expr* get_candidate_unsat();
        void check_restart();
        void ucb_forget();
        void initialize_bool_assignment();
        void finalize_bool_assignment();

    public:
        arith_lookahead(arith_base<num_t>& a);
        void search();
    };
}


