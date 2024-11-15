/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    theory_sls
    
Abstract:

    Interface to Concurrent SLS solver
    
Author:

    Nikolaj Bjorner (nbjorner) 2024-10-24

--*/
#pragma once


#include "util/rlimit.h"
#include "ast/sls/sat_ddfw.h"
#include "smt/smt_theory.h"
#include "model/model.h"


#ifdef SINGLE_THREAD

namespace smt {
    class theory_sls : public theory {
        model_ref m_model;
    public:
        theory_sls(context& ctx);
        ~theory_sls() override {}
        model_ref get_model() { return m_model; }
        char const* get_name() const override { return "sls"; }
        smt::theory* mk_fresh(context* new_ctx) override { return alloc(theory_sls, *new_ctx); }
        void display(std::ostream& out) const override {}
        bool internalize_atom(app* atom, bool gate_ctx) override { return false; }
        bool internalize_term(app* term) override { return false; }
        void new_eq_eh(theory_var v1, theory_var v2) override {}
        void new_diseq_eh(theory_var v1, theory_var v2) override {}
    };
}

#else

#include "ast/sls/sls_smt_plugin.h"


namespace smt {

    class theory_sls : public theory, public sls::smt_context {
        model_ref m_model;
        sls::smt_plugin* m_smt_plugin = nullptr;
        unsigned m_trail_lim = 0;
        bool m_checking = false;
        bool m_parallel_mode = true;
        unsigned m_threshold = 1;
        unsigned m_restart_sls_count = 0;
        unsigned m_difference_score = 0;
        unsigned m_difference_score_threshold = 0;
        unsigned m_num_guided_sls = 0;
        unsigned m_restart_ls_steps = 100000;
        unsigned m_restart_ls_steps_inc = 10000;
        unsigned m_restart_ls_steps_max = 300000;
        unsigned m_final_check_ls_steps = 30000;
        unsigned m_final_check_ls_steps_dec = 10000;
        unsigned m_final_check_ls_steps_min = 10000;
        ::statistics m_st;

        void finalize();
        void bounded_run(unsigned num_steps);
        void inc_restart_ls_steps() {
            if (m_restart_ls_steps < m_restart_ls_steps_max)
                m_restart_ls_steps += m_restart_ls_steps_inc;
        }
        void dec_final_check_ls_steps() {
            if (m_final_check_ls_steps > m_final_check_ls_steps_min)
                m_final_check_ls_steps -= m_final_check_ls_steps_dec;
        }

    public:
        theory_sls(context& ctx);
        ~theory_sls() override;
        model_ref get_model() { return m_model; }

        // smt::theory interface
        char const* get_name() const override { return "sls"; }
        void init() override;
        void pop_scope_eh(unsigned n) override;
        smt::theory* mk_fresh(context* new_ctx) override { return alloc(theory_sls, *new_ctx); }
        void collect_statistics(::statistics& st) const override;
        void propagate() override;
        void display(std::ostream& out) const override;
        bool internalize_atom(app * atom, bool gate_ctx) override { return false; }
        bool internalize_term(app* term) override { return false; }
        void new_eq_eh(theory_var v1, theory_var v2) override {}
        void new_diseq_eh(theory_var v1, theory_var v2) override {}
        void restart_eh() override;
        final_check_status final_check_eh() override;

        // sls::smt_context interface
        ast_manager& get_manager() override { return m; }
        params_ref get_params() override;
        void set_value(expr* t, expr* v) override;
        void force_phase(sat::literal lit) override;
        void set_has_new_best_phase(bool b) override;
        bool get_best_phase(sat::bool_var v) override;
        expr* bool_var2expr(sat::bool_var v) override;
        void set_finished() override;
        unsigned get_num_bool_vars() const override;
        void inc_activity(sat::bool_var v, double inc) override;
        bool parallel_mode() const { return m_parallel_mode; }
        bool get_value(expr* v, expr_ref& value) override;
    };

}

#endif
