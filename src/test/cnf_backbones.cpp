/*++
Copyright (c) 2017 Microsoft Corporation

--*/
#include<iostream>
#include<time.h>
#include<signal.h>
#include"timeout.h"
#include"rlimit.h"
#include"dimacs.h"
#include"sat_solver.h"
#include"gparams.h"

static sat::solver * g_solver = 0;
static clock_t       g_start_time;

static void display_statistics() {
    clock_t end_time = clock();
    if (g_solver) {
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

static void STD_CALL on_ctrl_c(int) {
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


static void cnf_backbones(char const* file_name) {
    g_start_time = clock();
    register_on_timeout_proc(on_timeout);
    signal(SIGINT, on_ctrl_c);
    params_ref p = gparams::get_module("sat");
    p.set_bool("produce_models", true);
    reslimit limit;
    sat::solver solver(p, limit, 0);
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
    
    vector<sat::literal_vector> conseq;
    sat::bool_var_vector vars;
    sat::literal_vector assumptions;
    for (unsigned i = 1; i < solver.num_vars(); ++i) {
        vars.push_back(i);        
        solver.set_external(i);
    }
    lbool r = solver.get_consequences(assumptions, vars, conseq);
    
    switch (r) {
    case l_true: 
        std::cout << "sat\n"; 
        std::cout << vars.size() << " " << conseq.size() << "\n";
        break;
    case l_undef: 
        std::cout << "unknown\n"; 
        break;
    case l_false: 
        std::cout << "unsat\n"; 
        break;
    }
    display_statistics();
}

void tst_cnf_backbones(char ** argv, int argc, int& i) {
    if (i + 1 < argc) {
        cnf_backbones(argv[i + 1]);
        ++i;
    }
}
