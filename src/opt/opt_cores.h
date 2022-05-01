/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    opt_cores.h

Abstract:
   
    "walk" subsets of soft constraints to extract multiple cores and satisfying assignments.

Author:

    Nikolaj Bjorner (nbjorner) 2022-04-27

--*/

#pragma once
#include "opt/opt_lns.h"

namespace opt {


    class cores {
        ast_manager&     m;
        solver&          s;
        lns_context&     ctx;

        random_gen               m_rand;
        rational                 m_best_cost = rational::minus_one();
        vector<weighted_core>    m_cores;
        obj_map<expr, rational>  m_weight;

        unsigned m_max_saturate_conflicts = 500;
        unsigned m_max_conflicts          = 1000;
        bool     m_hill_climb             = true;
        unsigned m_max_num_cores          = UINT_MAX;
        unsigned m_max_core_size          = 4;
        bool     m_enable_core_rotate     = false;

        struct scoped_update;

        bool improve();
        void rotate_rec(obj_hashtable<expr> const& mss, obj_map<expr, ptr_vector<expr>>& backbone2core, unsigned depth);
        bool rotate(obj_hashtable<expr> const& mss, expr* excl, unsigned depth);
        void saturate_core(expr_ref_vector& core);
        void local_mss();
        void hitting_set(obj_hashtable<expr>& hs);
        rational core_weight(expr_ref_vector const& core) { return core_weight(core.size(), core.data()); }
        rational core_weight(ptr_vector<expr> const& core) { return core_weight(core.size(), core.data()); }
        rational core_weight(unsigned sz, expr* const* core);
        lbool check_sat_hill_climb(expr_ref_vector const& _soft);

        void add_core(expr_ref_vector const& core);

        vector<weighted_core> const& disjoint_cores();

        void rotate_cores();

        vector<weighted_core> const& weighted_disjoint_cores();

        expr_ref_vector unsat_core();

    public:
        cores(solver& s, lns_context& ctx);
        
        vector<weighted_core> const& operator()();

        void updt_params(params_ref& p);
    };
};
