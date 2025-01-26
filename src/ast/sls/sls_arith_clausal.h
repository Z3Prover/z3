/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    sls_arith_clausal

Abstract:

    Theory plugin for arithmetic local search 
    based on clausal search as used in HybridSMT

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

    template<typename num_t>
    class arith_clausal {
        context& ctx;
        class arith_base<num_t>& a;

        void check_restart();
        void initialize();

        enum move_t {
            unsat_var_move,
            false_literal_move,
            random_move
        };
        friend std::ostream& operator<<(std::ostream& out, move_t mt) { 
            return out << (mt == unsat_var_move ? 
                "unsat-var" : mt == false_literal_move ? 
                "false-literal" : "random"); 
        }
        void enter_arith_mode();
        void enter_bool_mode();

        bool update_outer_best_solution();
        bool update_inner_best_solution();
        bool update_best_solution();
        var_t move_arith_variable();
        var_t critical_move_on_updates(move_t mt);
        var_t random_move_on_updates();
        void add_lookahead_on_unsat_vars();
        void add_lookahead_on_false_literals();
        void critical_move(var_t v, num_t const& delta, move_t mt);
        void lookahead(var_t v, num_t const& delta);
        double get_score(var_t v, num_t const& delta);
        void add_lookahead(sat::bool_var bv);
        

        unsigned m_no_improve_bool = 0;
        unsigned m_no_improve_arith = 0;
        unsigned m_no_improve = 0;
        bool     m_bool_mode = true;
        unsigned m_best_found_cost_bool = 0;
        unsigned m_best_found_cost_arith = 0;
        unsigned m_best_found_cost_restart = 0;
        unsigned m_best_found_cost = 0;
        num_t    m_best_abs_value;
        num_t    m_best_delta;
        var_t    m_best_var = UINT_MAX;
        unsigned m_best_last_step = 0;
        unsigned m_num_lookaheads = 0;
        double   m_best_score = 0;
        unsigned m_num_clauses = 0;

        // avoid checking the same updates twice
        var_t m_last_var = UINT_MAX;
        num_t m_last_delta;

    public:
        arith_clausal(arith_base<num_t>& a);
        void search();
    };
}


