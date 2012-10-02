/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    dimacs_frontend.cpp

Abstract:

    Frontend for reading dimacs input files

Author:

    Leonardo de Moura (leonardo) 2011-07-26.

Revision History:

--*/
#include<iostream>
#include<time.h>
#include<signal.h>
#include"timeout.h"
#include"dimacs.h"
#include"sat_solver.h"
#include"front_end_params.h"

extern bool          g_display_statistics;
static sat::solver * g_solver = 0;
static clock_t       g_start_time;

static void display_statistics() {
    clock_t end_time = clock();
    if (g_solver && g_display_statistics) {
        std::cout.flush();
        std::cerr.flush();
        
        statistics st;
        g_solver->collect_statistics(st);
        st.update("total time", ((static_cast<double>(end_time) - static_cast<double>(g_start_time)) / CLOCKS_PER_SEC));
        st.display_smt2(std::cout);
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

static void display_model(sat::solver const & s) {
    sat::model const & m = s.get_model();
    for (unsigned i = 1; i < m.size(); i++) {
        switch (m[i]) {
        case l_false: std::cout << "-" << i << " ";  break;
        case l_undef: break;
        case l_true: std::cout << i << " ";  break;
        }
    }
    std::cout << "\n";
}

unsigned read_dimacs(char const * file_name, front_end_params & front_end_params) {
    g_start_time = clock();
    register_on_timeout_proc(on_timeout);
    signal(SIGINT, on_ctrl_c);
    params_ref p;
    p.set_bool(":produce-models", front_end_params.m_model);
    sat::solver solver(p, 0);
    g_solver = &solver;

    if (file_name) {
        std::ifstream in(file_name);
        if (in.bad() || in.fail()) {
            std::cerr << "(error \"failed to open file '" << file_name << "'\")" << std::endl;
            exit(ERR_OPEN_FILE);
        }
        parse_dimacs(in, solver);
    }
    else {
        parse_dimacs(std::cin, solver);
    }
    IF_VERBOSE(20, solver.display_status(verbose_stream()););
    
    lbool r = solver.check();
    switch (r) {
    case l_true: 
        std::cout << "sat\n"; 
        if (front_end_params.m_model)
            display_model(solver);
        break;
    case l_undef: 
        std::cout << "unknown\n"; 
        break;
    case l_false: 
        std::cout << "unsat\n"; 
        break;
    }
    if (g_display_statistics)
        display_statistics();
    return 0;
}
