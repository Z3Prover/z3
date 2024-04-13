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
#include "ast/sls/bv_sls.h"
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

#include <thread>
#include <mutex>

namespace euf {
    class solver;
}

namespace sls {

    class solver : public euf::th_euf_solver {
        std::atomic<lbool> m_result;
        std::atomic<bool> m_completed, m_has_units;
        std::thread m_thread;
        std::mutex  m_mutex;
        // m is accessed by the main thread
        // m_slsm is accessed by the sls thread
        // m_shared is only accessed at synchronization points
        scoped_ptr<ast_manager> m_shared, m_slsm;
        scoped_ptr<bv::sls> m_sls;
        scoped_ptr<expr_ref_vector> m_units;
        model_ref m_model;
        unsigned m_trail_lim = 0;
        statistics m_st;

        void run_local_search();
        void sample_local_search();
        bool is_unit(expr*);

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
        sat::check_result check() override;
        std::ostream & display(std::ostream & out) const override { return out; }
        std::ostream & display_justification(std::ostream & out, sat::ext_justification_idx idx) const override { UNREACHABLE(); return out; }
        std::ostream & display_constraint(std::ostream & out, sat::ext_constraint_idx idx) const override { UNREACHABLE(); return out; }
        
    };

}

#endif