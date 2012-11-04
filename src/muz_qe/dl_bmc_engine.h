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

#ifndef _DL_BMC_ENGINE_H_
#define _DL_BMC_ENGINE_H_

#include "params.h"
#include "statistics.h"
#include "smt_kernel.h"
#include "bv_decl_plugin.h"


namespace datalog {
    class context;

    class bmc {
        context&         m_ctx;
        ast_manager&     m;
        front_end_params m_fparams;
        smt::kernel      m_solver;
        obj_map<func_decl, sort*> m_pred2sort;
        obj_map<sort, func_decl*> m_sort2pred;
        obj_map<func_decl, func_decl*> m_pred2newpred;
        obj_map<func_decl, ptr_vector<func_decl> > m_pred2args;
        ast_ref_vector   m_pinned;
        rule_set         m_rules;
        func_decl_ref    m_query_pred;
        expr_ref         m_answer;
        volatile bool    m_cancel;
        proof_converter_ref m_pc;
        sort_ref         m_path_sort;
        bv_util          m_bv;
        unsigned         m_bit_width;

        lbool check_query();

        proof_ref get_proof(model_ref& md, app* trace, app* path);

        void checkpoint();

        void declare_datatypes();

        void compile_nonlinear();

        void mk_rule_vars_nonlinear(rule& r, unsigned rule_id, expr* trace_arg, expr* path_arg, expr_ref_vector& sub);

        expr_ref mk_var_nonlinear(func_decl* pred, sort* s, unsigned idx, expr* path_arg, expr* trace_arg);

        expr_ref mk_arg_nonlinear(func_decl* pred, unsigned idx, expr* path_arg, expr* trace_arg);

        void mk_subst(rule& r, expr* path, app* trace, expr_ref_vector& sub);

        bool is_linear() const;

        lbool check_nonlinear();
        void  setup_nonlinear();
        bool check_model_nonlinear(model_ref& md, expr* trace);
        void mk_answer_nonlinear(model_ref& md, expr_ref& trace, expr_ref& path);
        
        func_decl_ref mk_predicate(func_decl* p);

        func_decl_ref mk_rule(func_decl* p, unsigned rule_idx);

        // linear check
        lbool check_linear();
        lbool check_linear(unsigned level);
        void compile_linear();
        void compile_linear(unsigned level);
        void compile_linear(rule& r, unsigned level);
        expr_ref mk_level_predicate(symbol const& name, unsigned level);
        expr_ref mk_level_predicate(func_decl* p, unsigned level);
        expr_ref mk_level_arg(func_decl* pred, unsigned idx, unsigned level);
        expr_ref mk_level_rule(func_decl* p, unsigned rule_idx, unsigned level);
        expr_ref mk_level_var(func_decl* pred, sort* s, unsigned rule_id, unsigned idx, unsigned level);
        void get_model_linear(unsigned level);
        void setup_linear();

        void assert_expr(expr* e);

        void mk_rule_vars(rule& r, unsigned level, unsigned rule_id, expr_ref_vector& sub);

        // quantified linear check
        void  compile_qlinear();
        void  setup_qlinear();
        lbool check_qlinear();
        lbool get_model_qlinear();
        sort_ref mk_index_sort();
        var_ref mk_index_var();
        void mk_qrule_vars(datalog::rule const& r, unsigned i, expr_ref_vector& sub);
        expr_ref mk_q_var(func_decl* pred, sort* s, unsigned rule_id, unsigned idx);
        expr_ref mk_q_arg(func_decl* pred, unsigned idx, bool is_current);
        expr_ref mk_q_one();
        expr_ref mk_q_num(unsigned i);
        expr_ref eval_q(model_ref& model, expr* t, unsigned i);
        expr_ref eval_q(model_ref& model, func_decl* f, unsigned i);
        func_decl_ref mk_q_rule(func_decl* f, unsigned rule_id);
        func_decl_ref mk_q_func_decl(func_decl* f);

    public:
        bmc(context& ctx);

        ~bmc();

        lbool query(expr* query);

        void cancel();

        void cleanup();

        void display_certificate(std::ostream& out) const;

        void collect_statistics(statistics& st) const;

        expr_ref get_answer();

        static void collect_params(param_descrs& p);
    };
};



#endif
