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

#include "util/params.h"
#include "util/statistics.h"
#include "smt/smt_kernel.h"
#include "ast/bv_decl_plugin.h"
#include "smt/params/smt_params.h"


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
        rule_ref_vector  m_rule_trace;

        void checkpoint();

        class nonlinear_dt;
        class nonlinear;
        class qlinear;
        class linear;

        bool is_linear() const;
        
        void assert_expr(expr* e);


    public:
        bmc(context& ctx);

        ~bmc() override;

        lbool query(expr* query) override;

        void display_certificate(std::ostream& out) const override;

        void collect_statistics(statistics& st) const override;

        void reset_statistics() override;
        void get_rules_along_trace(datalog::rule_ref_vector& rules) override;

        expr_ref get_answer() override;

        // direct access to (new) non-linear compiler.
        void compile(rule_set const& rules, expr_ref_vector& fmls, unsigned level);
        expr_ref compile_query(func_decl* query_pred, unsigned level);
    };
};



#endif
