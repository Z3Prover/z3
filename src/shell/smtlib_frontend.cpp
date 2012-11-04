/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smtlib_frontend.cpp

Abstract:

    Frontend for reading Smtlib input files

Author:

    Nikolaj Bjorner (nbjorner) 2006-11-3.

Revision History:

    Leonardo de Moura: new SMT 2.0 front-end, removed support for .smtc files and smtcmd_solver object.

--*/
#include<iostream>
#include<time.h>
#include<signal.h>
#include"smtlib_solver.h"
#include"timeout.h"
#include"smt2parser.h"
#include"dl_cmds.h"
#include"dbg_cmds.h"
#include"polynomial_cmds.h"
#include"subpaving_cmds.h"
#include"smt_strategic_solver.h"

#include"tactic2solver.h"
#include"qfnra_nlsat_tactic.h"

extern bool g_display_statistics;
extern void display_config();
static clock_t             g_start_time;
static smtlib::solver*     g_solver      = 0;
static cmd_context *       g_cmd_context = 0;

static void display_statistics() {
    display_config();
    clock_t end_time = clock();
    if ((g_solver || g_cmd_context) && g_display_statistics) {
        std::cout.flush();
        std::cerr.flush();
        if (g_solver) {
            g_solver->display_statistics();
            memory::display_max_usage(std::cout);
            std::cout << "time:               " << ((static_cast<double>(end_time) - static_cast<double>(g_start_time)) / CLOCKS_PER_SEC) << " secs\n";
        }
        else if (g_cmd_context) {
            g_cmd_context->set_regular_stream("stdout");
            g_cmd_context->display_statistics(true, ((static_cast<double>(end_time) - static_cast<double>(g_start_time)) / CLOCKS_PER_SEC));
        }
    }
}

static void on_timeout() {
    display_statistics();
    exit(0);
}

static void on_ctrl_c(int) {
    signal (SIGINT, SIG_DFL);
    display_statistics();
    raise(SIGINT);
}

unsigned read_smtlib_file(char const * benchmark_file, front_end_params & front_end_params) {
    g_start_time = clock();
    register_on_timeout_proc(on_timeout);
    signal(SIGINT, on_ctrl_c);
    smtlib::solver solver(front_end_params);
    g_solver = &solver;
    
    bool ok = true;
    
    ok = solver.solve_smt(benchmark_file);
    if (!ok) {
        if (benchmark_file) {
            std::cerr << "ERROR: solving '" << benchmark_file << "'.\n";
        }
        else {
            std::cerr << "ERROR: solving input stream.\n";
        }
    }
    
    display_statistics();
    register_on_timeout_proc(0);
    g_solver = 0;
    return solver.get_error_code();
}

unsigned read_smtlib2_commands(char const* file_name, front_end_params& front_end_params) {
    g_start_time = clock();
    register_on_timeout_proc(on_timeout);
    signal(SIGINT, on_ctrl_c);
    cmd_context ctx(&front_end_params);

    // temporary hack until strategic_solver is ported to new tactic framework
    if (front_end_params.m_nlsat) {
        tactic_factory2solver * s = alloc(tactic_factory2solver);
        s->set_tactic(alloc(qfnra_nlsat_fct));
        ctx.set_solver(s);
    }
    else {
        solver * s = mk_smt_strategic_solver(false);
        ctx.set_solver(s);
    }
    install_dl_cmds(ctx);
    install_dbg_cmds(ctx);
    install_polynomial_cmds(ctx);
    install_subpaving_cmds(ctx);

    g_cmd_context = &ctx;
    register_on_timeout_proc(on_timeout);
    signal(SIGINT, on_ctrl_c);
    
    bool result = true;
    if (file_name) {
        std::ifstream in(file_name);
        if (in.bad() || in.fail()) {
            std::cerr << "(error \"failed to open file '" << file_name << "'\")" << std::endl;
            exit(ERR_OPEN_FILE);
        }
        result = parse_smt2_commands(ctx, in);
    }
    else {
        result = parse_smt2_commands(ctx, std::cin, true);
    }
    
    display_statistics();
    g_cmd_context = 0;
    return result ? 0 : 1;
}

