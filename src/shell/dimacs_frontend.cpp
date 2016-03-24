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
#include"rlimit.h"
#include"dimacs.h"
#include"sat_solver.h"
#include"gparams.h"

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

static void display_core(sat::solver const& s, vector<sat::literal_vector> const& tracking_clauses) {
    std::cout << "core\n";
    sat::literal_vector const& c = s.get_core();
    for (unsigned i = 0; i < c.size(); ++i) {
        sat::literal_vector const& cls = tracking_clauses[c[i].var()];
        for (unsigned j = 0; j < cls.size(); ++j) {
            std::cout << cls[j] << " ";
        }
        std::cout << "\n";
    }
}

static void track_clause(sat::solver& dst,
                         sat::literal_vector& lits,
                         sat::literal_vector& assumptions,
                         vector<sat::literal_vector>& tracking_clauses) {
    sat::literal lit = sat::literal(dst.mk_var(true, false), false);
    tracking_clauses.set(lit.var(), lits);
    lits.push_back(~lit);
    dst.mk_clause(lits.size(), lits.c_ptr());
    assumptions.push_back(lit);            
}


static void track_clauses(sat::solver const& src, 
                          sat::solver& dst, 
                          sat::literal_vector& assumptions,
                          vector<sat::literal_vector>& tracking_clauses) {
    for (sat::bool_var v = 0; v < src.num_vars(); ++v) {
        dst.mk_var(false, true);
    }
    sat::literal_vector lits;
    sat::literal lit;
    sat::clause * const * it  = src.begin_clauses();
    sat::clause * const * end = src.end_clauses();
    svector<sat::solver::bin_clause> bin_clauses;
    src.collect_bin_clauses(bin_clauses, false);
    tracking_clauses.reserve(2*src.num_vars() + static_cast<unsigned>(end - it) + bin_clauses.size());

    for (sat::bool_var v = 1; v < src.num_vars(); ++v) {
        if (src.value(v) != l_undef) {
            bool sign = src.value(v) == l_false;
            lits.reset();
            lits.push_back(sat::literal(v, sign));
            track_clause(dst, lits, assumptions, tracking_clauses);
        }
    }
    for (; it != end; ++it) {
        lits.reset();
        sat::clause& cls = *(*it);
        lits.append(static_cast<unsigned>(cls.end()-cls.begin()), cls.begin());
        track_clause(dst, lits, assumptions, tracking_clauses);
    }
    for (unsigned i = 0; i < bin_clauses.size(); ++i) {
        lits.reset();
        lits.push_back(bin_clauses[i].first);
        lits.push_back(bin_clauses[i].second);        
        track_clause(dst, lits, assumptions, tracking_clauses);
    }
}


unsigned read_dimacs(char const * file_name) {
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
    
    lbool r;
    vector<sat::literal_vector> tracking_clauses;
    sat::solver solver2(p, limit, 0);
    if (p.get_bool("dimacs.core", false)) {
        g_solver = &solver2;        
        sat::literal_vector assumptions;
        track_clauses(solver, solver2, assumptions, tracking_clauses);
        r = g_solver->check(assumptions.size(), assumptions.c_ptr());
    }
    else {
        r = g_solver->check();
    }
    switch (r) {
    case l_true: 
        std::cout << "sat\n"; 
        display_model(*g_solver);
        break;
    case l_undef: 
        std::cout << "unknown\n"; 
        break;
    case l_false: 
        std::cout << "unsat\n"; 
        if (p.get_bool("dimacs.core", false)) {
            display_core(*g_solver, tracking_clauses);
        }
        break;
    }
    if (g_display_statistics)
        display_statistics();
    return 0;
}
