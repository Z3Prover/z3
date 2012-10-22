/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smtlib_solver.h

Abstract:

    SMT based solver.

Author:

    Nikolaj Bjorner (nbjorner) 2006-11-3.

Revision History:

--*/
#ifndef _SMTLIB_SOLVER_H_
#define _SMTLIB_SOLVER_H_

#include"smtparser.h"
#include"front_end_params.h"
#include"lbool.h"

class cmd_context;

namespace smtlib  {    
    class solver {
        ast_manager         m_ast_manager;
        front_end_params &  m_params;
        cmd_context *       m_ctx;
        scoped_ptr<parser>  m_parser;
        unsigned            m_error_code;
    public:
        solver(front_end_params & params);
        ~solver(); 
        bool solve_smt(char const * benchmark_file);
        bool solve_smt_string(char const * benchmark_string);
        void display_statistics();
        unsigned get_error_code() const { return m_error_code; }
    private:
        void solve_benchmark(benchmark & benchmark);
        void solve_formula(benchmark const & benchmark, expr * f);
    };
};

#endif
