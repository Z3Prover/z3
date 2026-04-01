/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    nseq_context_solver.h

Abstract:

    context_solver: concrete implementation of seq::simple_solver
    that delegates arithmetic feasibility checks to an smt::kernel
    configured with seq.solver = "seq_len".

Author:

    Nikolaj Bjorner (nbjorner) 2026-03-10

--*/
#pragma once

#include "smt/seq/seq_nielsen.h"
#include "smt/smt_kernel.h"
#include "smt/smt_arith_value.h"
#include "params/smt_params.h"

namespace smt {

    /**
     * Concrete simple_solver that wraps smt::kernel.
     * Initializes the kernel with seq.solver = "seq_len" so that
     * sequence length constraints are handled by theory_seq_len.
     */
    class context_solver : public seq::simple_solver {
        smt_params  m_params;  // must be declared before m_kernel
        kernel m_kernel;
        arith_value m_arith_value;

        static smt_params make_seq_len_params() {
            smt_params p;
            p.m_string_solver = symbol("seq_len");
            return p;
        }

    public:
        context_solver(ast_manager& m) :
            m_params(make_seq_len_params()),
            m_kernel(m, m_params),
            m_arith_value(m) {
            m_arith_value.init(&m_kernel.get_context());
        }

        lbool check() override {
            // std::cout << "Checking:\n";
            // for (int i = 0; i < m_kernel.size(); i++) {
            //     std::cout << "\t" << mk_pp(m_kernel.get_formula(i), m_kernel.m()) << std::endl;
            // }
            // std::cout << std::endl;
            // std::cout << "Checking" << std::endl;
            // for (unsigned i = 0; i < m_kernel.size(); i++) {
            //     std::cout << mk_pp(m_kernel.get_formula(i), m_kernel.m()) << std::endl;
            // }
            return m_kernel.check();
        }

        void assert_expr(expr* e) override {
            m_kernel.assert_expr(e);
        }

        void push() override {
            m_kernel.push();
        }

        void pop(unsigned num_scopes) override {
            m_kernel.pop(num_scopes);
        }

        void get_model(model_ref& mdl) override {
            m_kernel.get_model(mdl);
        }

        bool lower_bound(expr* e, rational& lo) const override {
            bool is_strict = true;
            return m_arith_value.get_lo(e, lo, is_strict) && !is_strict && lo.is_int();
        }

        bool upper_bound(expr* e, rational& hi) const override {
            bool is_strict = true;
            return m_arith_value.get_up(e, hi, is_strict) && !is_strict && hi.is_int();
        }

        bool current_value(expr* e, rational& v) const override {
            return m_arith_value.get_value(e, v) && v.is_int(); 
        }            

        lbool check_with_assumptions(expr_ref_vector& assumptions, expr_ref_vector& core) override {
            // TODO: Not ideal
            // Replay with assumptions
            // std::cout << "Assuming" << std::endl;
            // for (unsigned i = 0; i < assumptions.size(); i++) {
            //     std::cout << mk_pp(assumptions[i].get(), m_kernel.m()) << std::endl;
            // }
            lbool r = m_kernel.check(assumptions.size(), assumptions.data());
            unsigned cnt = m_kernel.get_unsat_core_size();
            core.resize(cnt);
            for (unsigned i = 0; i < cnt; i++) {
                core[i] = m_kernel.get_unsat_core_expr(i);
            }
            return r;
         }

        void reset() override {
            m_kernel.reset();
            m_arith_value.init(&m_kernel.get_context());
        }
    };

}
