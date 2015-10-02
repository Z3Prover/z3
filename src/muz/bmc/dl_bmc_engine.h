/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    dl_bmc_engine.h

Abstract:

    BMC engine for fixedpoint solver.

Author:

    Nikolaj Bjorner (nbjorner) 2012-9-20

Revision History:

--*/

#ifndef DL_BMC_ENGINE_H_
#define DL_BMC_ENGINE_H_

#include "params.h"
#include "statistics.h"
#include "smt_kernel.h"
#include "bv_decl_plugin.h"
#include "smt_params.h"


namespace datalog {
    class context;

    class bmc : public engine_base {
        context&         m_ctx;
        ast_manager&     m;
        smt_params       m_fparams;
        smt::kernel      m_solver;
        rule_set         m_rules;
        func_decl_ref    m_query_pred;
        expr_ref         m_answer;
        volatile bool    m_cancel;

        void checkpoint();

        class nonlinear_dt;
        class nonlinear;
        class qlinear;
        class linear;

        bool is_linear() const;
        
        void assert_expr(expr* e);


    public:
        bmc(context& ctx);

        ~bmc();

        lbool query(expr* query);

        void cancel();

        void cleanup();

        void display_certificate(std::ostream& out) const;

        void collect_statistics(statistics& st) const;

        void reset_statistics(); 

        expr_ref get_answer();

        // direct access to (new) non-linear compiler.
        void compile(rule_set const& rules, expr_ref_vector& fmls, unsigned level);
        expr_ref compile_query(func_decl* query_pred, unsigned level);
    };
};



#endif
