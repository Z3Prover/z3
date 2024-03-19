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

#include <thread>
#include "util/rlimit.h"
#include "ast/sls/bv_sls.h"
#include "sat/smt/sat_th.h"


namespace euf {
    class solver;
}

namespace sls {

    class solver : public euf::th_euf_solver {
        std::atomic<lbool> m_result;
        std::atomic<bool> m_completed;
        std::thread m_thread;
        scoped_ptr<ast_manager> m_m;
        scoped_ptr<bv::sls> m_bvsls;

        void run_local_search();
        void init_local_search();
        void sample_local_search();
    public:
        solver(euf::solver& ctx);
        ~solver();

        void push_core() override;
        void pop_core(unsigned n) override;
        void simplify() override;

        sat::literal internalize(expr* e, bool sign, bool root) override { UNREACHABLE();  return sat::null_literal; }
        void internalize(expr* e) override { UNREACHABLE(); }
        th_solver* clone(euf::solver& ctx) override { return alloc(solver, ctx); }
       

        bool unit_propagate() override { return false; }
        void get_antecedents(sat::literal l, sat::ext_justification_idx idx, sat::literal_vector & r, bool probing) override { UNREACHABLE(); }
        sat::check_result check() override { return sat::check_result::CR_DONE; }
        std::ostream & display(std::ostream & out) const override { return out; }
        std::ostream & display_justification(std::ostream & out, sat::ext_justification_idx idx) const override { UNREACHABLE(); return out; }
        std::ostream & display_constraint(std::ostream & out, sat::ext_constraint_idx idx) const override { UNREACHABLE(); return out; }
        
    };

}
