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

namespace sls {
    class theory_sls : public smt::theory {
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
    class context;

    class theory_sls : public smt::theory, public sls::smt_context {
        model_ref m_model;
        sls::smt_plugin* m_smt_plugin = nullptr;
        unsigned m_trail_lim = 0;
        bool m_checking = false;
        ::statistics m_st;

        void finalize();

    public:
        theory_sls(context& ctx);
        ~theory_sls() override;
        model_ref get_model() { return m_model; }
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

        ast_manager& get_manager() override { return m; }
        params_ref get_params() override;
        void initialize_value(expr* t, expr* v) override;
        void force_phase(sat::literal lit) override;
        void set_has_new_best_phase(bool b) override;
        bool get_best_phase(sat::bool_var v) override;
        expr* bool_var2expr(sat::bool_var v) override;
        void set_finished() override;
        unsigned get_num_bool_vars() const override;

    };

}

#endif
