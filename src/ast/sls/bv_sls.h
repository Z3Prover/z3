/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    bv_sls.h

Abstract:

    A Stochastic Local Search (SLS) engine

Author:

    Nikolaj Bjorner (nbjorner) 2024-02-07
    
--*/
#pragma once

#include "util/lbool.h"
#include "util/params.h"
#include "util/scoped_ptr_vector.h"
#include "util/uint_set.h"
#include "ast/ast.h"
#include "ast/sls/sls_stats.h"
#include "ast/sls/sls_powers.h"
#include "ast/sls/sls_valuation.h"
#include "ast/sls/bv_sls_terms.h"
#include "ast/sls/bv_sls_eval.h"
#include "ast/sls/sls_engine.h"
#include "ast/bv_decl_plugin.h"
#include "model/model.h"

namespace bv {


    class sls {

        struct config {
            unsigned    m_max_restarts = 1000;
            unsigned    m_max_repairs = 1000;
        };

        ast_manager&        m;
        bv_util             bv;
        sls_terms           m_terms;
        sls_eval            m_eval;
        sls_stats           m_stats;
        indexed_uint_set    m_repair_up, m_repair_roots;
        unsigned            m_repair_down = UINT_MAX;
        ptr_vector<expr>    m_todo;
        random_gen          m_rand;
        config              m_config;
        sls_engine          m_engine;
        bool                m_engine_model = false;
        bool                m_engine_init = false;
        std::function<expr_ref()> m_get_unit;
        std::function<void(model& mdl)> m_set_model;
        unsigned            m_min_repair_size = UINT_MAX;
        
        std::pair<bool, app*> next_to_repair();
        
        void init_repair_goal(app* e);
        void set_model();
        void try_repair_down(app* e);
        void try_repair_up(app* e);
        void set_repair_down(expr* e) { m_repair_down = e->get_id(); }

        lbool search1();
        lbool search2();
        void reinit_eval();
        void init_repair();
        void trace();
        std::ostream& trace_repair(bool down, expr* e);

        indexed_uint_set m_to_repair;
        void init_repair_candidates();

    public:
        sls(ast_manager& m, params_ref const& p);
                
        /**
        * Add constraints
        */
        void assert_expr(expr* e) { m_terms.assert_expr(e); m_engine.assert_expr(e); }

        /*
        * Invoke init after all expressions are asserted. 
        */
        void init();

        /**
        * Invoke init_eval to initialize, or re-initialize, values of
        * uninterpreted constants.
        */
        void init_eval(std::function<bool(expr*, unsigned)>& eval);

        /**
        * add callback to retrieve new units
        */
        void init_unit(std::function<expr_ref()> get_unit) { m_get_unit = get_unit; }

        /**
        * Add callback to set model
        */
        void set_model(std::function<void(model& mdl)> f) { m_set_model = f; }

        /**
        * Run (bounded) local search to find feasible assignments.
        */
        lbool operator()();

        void updt_params(params_ref const& p);
        void collect_statistics(statistics& st) const { m_stats.collect_statistics(st); m_engine.collect_statistics(st); }
        void reset_statistics() { m_stats.reset(); m_engine.reset_statistics(); }

        unsigned get_num_moves() { return m_stats.m_moves + m_engine.get_stats().m_moves; }

        std::ostream& display(std::ostream& out);

        /**
        * Retrieve valuation
        */
        sls_valuation const& wval(expr* e) const { return m_eval.wval(e); }

        model_ref get_model();

        void cancel() { m.limit().cancel(); }
    };
}
