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
#include "util/timeout.h"
#include "parsers/smt2/smt2parser.h"
#include "muz/fp/dl_cmds.h"
#include "cmd_context/extra_cmds/dbg_cmds.h"
#include "opt/opt_cmds.h"
#include "cmd_context/extra_cmds/polynomial_cmds.h"
#include "cmd_context/extra_cmds/subpaving_cmds.h"
#include "smt/smt2_extra_cmds.h"
#include "tactic/portfolio/smt_strategic_solver.h"
#include "smt/smt_solver.h"

extern bool g_display_statistics;
static clock_t             g_start_time;
static cmd_context *       g_cmd_context = nullptr;

static void display_statistics() {
    clock_t end_time = clock();
    if (g_cmd_context && g_display_statistics) {
        std::cout.flush();
        std::cerr.flush();
        if (g_cmd_context) {
            g_cmd_context->set_regular_stream("stdout");
            g_cmd_context->display_statistics(true, ((static_cast<double>(end_time) - static_cast<double>(g_start_time)) / CLOCKS_PER_SEC));
        }
    }
}

static void on_timeout() {
    #pragma omp critical (g_display_stats)
    {
        display_statistics();
        exit(0);
    }
}

static void STD_CALL on_ctrl_c(int) {
    signal (SIGINT, SIG_DFL);
    #pragma omp critical (g_display_stats)
    {
        display_statistics();
    }
    raise(SIGINT);
}


unsigned read_smtlib2_commands(char const * file_name) {
    g_start_time = clock();
    register_on_timeout_proc(on_timeout);
    signal(SIGINT, on_ctrl_c);
    cmd_context ctx;

    ctx.set_solver_factory(mk_smt_strategic_solver_factory());

    install_dl_cmds(ctx);
    install_dbg_cmds(ctx);
    install_polynomial_cmds(ctx);
    install_subpaving_cmds(ctx);
    install_opt_cmds(ctx);
    install_smt2_extra_cmds(ctx);

    g_cmd_context = &ctx;
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


    #pragma omp critical (g_display_stats)
    {
        display_statistics();
        g_cmd_context = nullptr;
    }
    return result ? 0 : 1;
}

