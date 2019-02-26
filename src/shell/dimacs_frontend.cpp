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
#include "util/timeout.h"
#include "util/rlimit.h"
#include "util/gparams.h"
#include "sat/dimacs.h"
#include "sat/sat_params.hpp"
#include "sat/sat_solver.h"
#include "sat/ba_solver.h"
#include "sat/tactic/goal2sat.h"
#include "ast/reg_decl_plugins.h"
#include "tactic/tactic.h"
#include "tactic/fd_solver/fd_solver.h"


extern bool          g_display_statistics;
static sat::solver * g_solver = nullptr;
static clock_t       g_start_time;
static tactic_ref    g_tac;
static statistics    g_st;

static void display_statistics() {
    clock_t end_time = clock();
    if (g_tac && g_display_statistics) {
        g_tac->collect_statistics(g_st);
    }
    if (g_solver && g_display_statistics) {
        std::cout.flush();
        std::cerr.flush();
        
        g_solver->collect_statistics(g_st);
        g_st.update("total time", ((static_cast<double>(end_time) - static_cast<double>(g_start_time)) / CLOCKS_PER_SEC));
        g_st.display_smt2(std::cout);
    }
    g_display_statistics = false;
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
    src.collect_bin_clauses(bin_clauses, false, false);
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

void verify_solution(char const * file_name) {
    params_ref p = gparams::get_module("sat");
    p.set_bool("produce_models", true);
    reslimit limit;
    sat::solver solver(p, limit);
    std::ifstream in(file_name);
    if (in.bad() || in.fail()) {
        std::cerr << "(error \"failed to open file '" << file_name << "'\")" << std::endl;
        exit(ERR_OPEN_FILE);
    }
    parse_dimacs(in, std::cerr, solver);
    
    sat::model const & m = g_solver->get_model();
    for (unsigned i = 1; i < m.size(); i++) {
        sat::literal lit(i, false);
        switch (m[i]) {
        case l_false: lit.neg(); break;
        case l_undef: break;
        case l_true: break;
        }
        solver.mk_clause(1, &lit);
    }
    lbool r = solver.check();
    switch (r) {
    case l_false: 
        std::cout << "model checking failed\n";
        break;
    case l_true:
        std::cout << "model validated\n";
        break;
    default:
        std::cout << "inconclusive model\n";
        break;
    }
}

lbool solve_parallel(sat::solver& s) {
    params_ref p = gparams::get_module("sat");
    ast_manager m;
    reg_decl_plugins(m);    
    sat2goal s2g;
    ref<sat2goal::mc> mc;
    atom2bool_var a2b(m);
    for (unsigned v = 0; v < s.num_vars(); ++v) {
        a2b.insert(m.mk_const(symbol(v), m.mk_bool_sort()), v);
    }
    goal_ref g = alloc(goal, m);         
    s2g(s, a2b, p, *g, mc);

    g_tac = mk_parallel_qffd_tactic(m, p);
    std::string reason_unknown;
    model_ref md;
    labels_vec labels;
    proof_ref pr(m);
    expr_dependency_ref core(m);
    lbool r = check_sat(*g_tac, g, md, labels, pr, core, reason_unknown);
    switch (r) {
    case l_true:
        if (gparams::get_ref().get_bool("model_validate", false)) {
            // populate the SAT solver with the model obtained from parallel execution.
            for (auto const& kv : a2b) {
                sat::literal lit;
                bool is_true = m.is_true((*md)(kv.m_key));
                lit = sat::literal(kv.m_value, !is_true);
                s.mk_clause(1, &lit);
            }
            // VERIFY(l_true == s.check());
        }
        break;
    case l_false:
        break;
    default:
        break;
    }
    display_statistics();
    g_display_statistics = false;    
    g_tac = nullptr;
    return r;
}

unsigned read_dimacs(char const * file_name) {
    g_start_time = clock();
    register_on_timeout_proc(on_timeout);
    signal(SIGINT, on_ctrl_c);
    params_ref p = gparams::get_module("sat");
    params_ref par = gparams::get_module("parallel");
    p.set_bool("produce_models", true);
    sat_params sp(p);
    reslimit limit;
    sat::solver solver(p, limit);
    if (sp.xor_solver()) {
        solver.set_extension(alloc(sat::ba_solver));
    }
    g_solver = &solver;

    if (file_name) {
        std::ifstream in(file_name);
        if (in.bad() || in.fail()) {
            std::cerr << "(error \"failed to open file '" << file_name << "'\")" << std::endl;
            exit(ERR_OPEN_FILE);
        }
        parse_dimacs(in, std::cerr, solver);
    }
    else {
        parse_dimacs(std::cin, std::cerr, solver);
    }
    IF_VERBOSE(20, solver.display_status(verbose_stream()););
    
    lbool r;
    vector<sat::literal_vector> tracking_clauses;
    params_ref p2;
    p2.copy(p);
    p2.set_sym("drat.file", symbol::null);
    
    sat::solver solver2(p2, limit);
    if (p.get_bool("dimacs.core", false)) {
        g_solver = &solver2;        
        sat::literal_vector assumptions;
        track_clauses(solver, solver2, assumptions, tracking_clauses);
        r = g_solver->check(assumptions.size(), assumptions.c_ptr());
    }
    else if (par.get_bool("enable", false)) {
        r = solve_parallel(solver);
    }
    else {
        r = g_solver->check();
    }
    switch (r) {
    case l_true: 
        std::cout << "sat\n"; 
        if (file_name && gparams::get_ref().get_bool("model_validate", false)) verify_solution(file_name);
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
    display_statistics();
    return 0;
}
