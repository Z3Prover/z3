/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smtlib_solver.cpp

Abstract:

    SMT based solver.

Author:

    Nikolaj Bjorner (nbjorner) 2006-11-3.

Revision History:

--*/

#include"smtparser.h"
#include"smtlib_solver.h"
#include"warning.h"
#include"ast_pp.h"
#include"ast_ll_pp.h"
#include"well_sorted.h"
#include"model.h"
#include"model_v2_pp.h"
#include"solver.h"
#include"smt_strategic_solver.h"
#include"cmd_context.h"

namespace smtlib {

    solver::solver(front_end_params & params):
        m_ast_manager(params.m_proof_mode, params.m_trace_stream),
        m_params(params),
        m_ctx(0),
        m_parser(parser::create(m_ast_manager, params.m_ignore_user_patterns)), 
        m_error_code(0) {
        m_parser->initialize_smtlib();
    }

    solver::~solver() {
        if (m_ctx)
            dealloc(m_ctx);
    }

    bool solver::solve_smt(char const * benchmark_file) {    
        IF_VERBOSE(100, verbose_stream() << "parsing...\n";);
        if (!m_parser->parse_file(benchmark_file)) {
            if (benchmark_file) {
                warning_msg("could not parse file '%s'.", benchmark_file);
            }
            else {
                warning_msg("could not parse input stream.");
            }
            m_error_code = ERR_PARSER;
            return false;
        }
        benchmark * benchmark = m_parser->get_benchmark();
        solve_benchmark(*benchmark);
        return true;
    }

    bool solver::solve_smt_string(char const * benchmark_string) {    
        if (!m_parser->parse_string(benchmark_string)) {
            warning_msg("could not parse string '%s'.", benchmark_string);
            return false;
        }
        benchmark * benchmark = m_parser->get_benchmark();
        solve_benchmark(*benchmark);
        return true;
    }
    
    void solver::display_statistics() {
        if (m_ctx)
            m_ctx->display_statistics();
    }

    void solver::solve_benchmark(benchmark & benchmark) {
        if (benchmark.get_num_formulas() == 0) {
            // Hack: it seems SMT-LIB allow benchmarks without any :formula
            benchmark.add_formula(m_ast_manager.mk_true());
        }
        m_ctx = alloc(cmd_context, &m_params, true, &m_ast_manager, benchmark.get_logic());
        m_ctx->set_solver(mk_smt_strategic_solver(false));
        theory::expr_iterator fit  = benchmark.begin_formulas();
        theory::expr_iterator fend = benchmark.end_formulas();
        for (; fit != fend; ++fit)
            solve_formula(benchmark, *fit);
    }

    void solver::solve_formula(benchmark const & benchmark, expr * f) {
        IF_VERBOSE(100, verbose_stream() << "starting...\n";);
        m_ctx->reset();
        for (unsigned i = 0; i < benchmark.get_num_axioms(); i++) 
            m_ctx->assert_expr(benchmark.get_axioms()[i]);
        m_ctx->assert_expr(f);
        m_ctx->check_sat(benchmark.get_num_assumptions(), benchmark.get_assumptions());
        check_sat_result * r = m_ctx->get_check_sat_result();
        if (r != 0) {
            proof * pr = r->get_proof();
            if (pr != 0 && m_params.m_display_proof)
                std::cout << mk_ll_pp(pr, m_ast_manager, false, false);
            model_ref md;
            if (r->status() != l_false) r->get_model(md);
            if (md.get() != 0 && m_params.m_model) {
                model_v2_pp(std::cout, *(md.get()), m_params.m_model_partial);
            }
        }
        else {
            m_error_code = ERR_UNKNOWN_RESULT;
        }
    }
};
