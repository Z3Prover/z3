/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    sls_solver

Abstract:

    Interface to Concurrent SLS solver
    
Author:

    Nikolaj Bjorner (nbjorner) 2024-02-21

--*/
#pragma once


#include "util/rlimit.h"
#include "ast/sls/sat_ddfw.h"
#include "sat/smt/sat_th.h"


#ifdef SINGLE_THREAD


namespace euf {
    class solver;
}

namespace sls {

    class solver : public euf::th_euf_solver {
    public:
        solver(euf::solver& ctx);
            
        sat::literal internalize(expr* e, bool sign, bool root) override { UNREACHABLE();  return sat::null_literal; }
        void internalize(expr* e) override { UNREACHABLE(); }
        th_solver* clone(euf::solver& ctx) override { return alloc(solver, ctx); }

        model_ref get_model() { return model_ref(nullptr); }
        bool unit_propagate() override { return false; }
        void get_antecedents(sat::literal l, sat::ext_justification_idx idx, sat::literal_vector& r, bool probing) override { UNREACHABLE(); }
        sat::check_result check() override { return sat::check_result::CR_DONE;}
        std::ostream& display(std::ostream& out) const override { return out; }
        std::ostream& display_justification(std::ostream& out, sat::ext_justification_idx idx) const override { UNREACHABLE(); return out; }
        std::ostream& display_constraint(std::ostream& out, sat::ext_constraint_idx idx) const override { UNREACHABLE(); return out; }

    };
}

#else

#include "ast/sls/sls_smt_plugin.h"

namespace euf {
    class solver;
}

namespace sls {

    class solver : public euf::th_euf_solver, public sls::smt_context {
        model_ref m_model;
        sls::smt_plugin* m_smt_plugin = nullptr;
        unsigned m_trail_lim = 0;
        bool m_checking = false;
        ::statistics m_st;

    public:
        solver(euf::solver& ctx);
        ~solver();

        model_ref get_model() { return m_model; }

        void init_search() override;
        void push_core() override {}
        void pop_core(unsigned n) override;
        th_solver* clone(euf::solver& ctx) override { return alloc(solver, ctx); }
        void collect_statistics(statistics& st) const override { st.copy(m_st); }       
        void finalize() override;
        bool unit_propagate() override;

        sat::literal internalize(expr* e, bool sign, bool root) override { UNREACHABLE();  return sat::null_literal; }
        void internalize(expr* e) override { UNREACHABLE(); }
        void get_antecedents(sat::literal l, sat::ext_justification_idx idx, sat::literal_vector & r, bool probing) override { UNREACHABLE(); }
        sat::check_result check() override { return sat::check_result::CR_DONE; }
        std::ostream& display(std::ostream& out) const override;
        std::ostream & display_justification(std::ostream & out, sat::ext_justification_idx idx) const override { UNREACHABLE(); return out; }
        std::ostream & display_constraint(std::ostream & out, sat::ext_constraint_idx idx) const override { UNREACHABLE(); return out; }


        ast_manager& get_manager() override { return m; }
        params_ref get_params() override;
        void set_value(expr* t, expr* v) override;
        void force_phase(sat::literal lit) override;
        void set_has_new_best_phase(bool b) override;
        bool get_best_phase(sat::bool_var v) override;
        expr* bool_var2expr(sat::bool_var v) override;
        void set_finished() override;
        void inc_activity(sat::bool_var v, double inc) override {}
        unsigned get_num_bool_vars() const override;
        bool parallel_mode() const override { return false; }
        bool get_smt_value(expr* v, expr_ref& value) override { return false; }
        
    };

}

#endif
