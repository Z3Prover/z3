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
#include "ast/bv_decl_plugin.h"
#include "model/model.h"

namespace bv {


    class sls {

        struct config {
            unsigned    m_max_restarts = 1000;
            unsigned    m_max_repairs = 100000;
        };

        ast_manager&        m;
        bv_util             bv;
        sls_terms           m_terms;
        sls_eval            m_eval;
        sls_stats           m_stats;
        indexed_uint_set    m_repair_down, m_repair_up;
        ptr_vector<expr>    m_todo;
        random_gen          m_rand;
        config              m_config;
        
        
        bool eval_is_correct(app* e);
        bool try_repair_down(app* e);
        bool try_repair_up(app* e);

        bool try_repair_down(app* e, unsigned i);

    public:
        sls(ast_manager& m);
                
        /**
        * Add constraints
        */
        void assert_expr(expr* e) { m_terms.assert_expr(e); }

        /*
        * Invoke init after all expressions are asserted. 
        * No other expressions can be asserted after init.
        */
        void init();

        /**
        * Invoke init_eval to initialize, or re-initialize, values of
        * uninterpreted constants.
        */
        void init_eval(std::function<bool(expr*, unsigned)>& eval);

        /**
        * Run (bounded) local search to find feasible assignments.
        */
        lbool operator()();

        void updt_params(params_ref const& p) {}
        void collect_statistics(statistics & st) const { m_stats.collect_statistics(st); }
        void reset_statistics() { m_stats.reset(); }

        sls_stats const& get_stats() const { return m_stats; }

        std::ostream& display(std::ostream& out);

        /**
        * Retrieve valuation
        */
        sls_valuation const& wval(expr* e) const { return m_eval.wval0(e); }

        model_ref get_model();
    };
}
