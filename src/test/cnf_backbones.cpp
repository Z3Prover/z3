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

static void display_status(lbool r) {
    switch (r) {
    case l_true: 
        std::cout << "sat\n"; 
        break;
    case l_undef: 
        std::cout << "unknown\n"; 
        break;
    case l_false: 
        std::cout << "unsat\n"; 
        break;
    }
}

static void prune_unfixed(sat::literal_vector& lambda, sat::model const& m) {
    for (unsigned i = 0; i < lambda.size(); ++i) {
        if ((m[lambda[i].var()] == l_false) != lambda[i].sign()) {
            lambda[i] = lambda.back();
            lambda.pop_back();
            --i;
        }
    }
}

// Algorithm 7: Corebased Algorithm with Chunking

static void back_remove(sat::literal_vector& lits, sat::literal l) {
    for (unsigned i = lits.size(); i > 0; ) {
        --i;
        if (lits[i] == l) {
            lits[i] = lits.back();
            lits.pop_back();
            return;
        }
    }
    std::cout << "UNREACHABLE\n";
}

static void brute_force_consequences(sat::solver& s, sat::literal_vector const& gamma, sat::literal_vector& backbones) {
    for (unsigned i = 0; i < gamma.size(); ++i) {
        sat::literal nlit = ~gamma[i];
        lbool r = s.check(1, &nlit);
        if (r == l_false) {
            backbones.push_back(gamma[i]);
        }
    }
}

static lbool core_chunking(sat::solver& s, sat::bool_var_vector& vars, vector<sat::literal_vector>& conseq, unsigned K) {
    lbool r = s.check();
    display_status(r);
    if (r != l_true) {
        return r;
    }
    sat::model const & m = s.get_model();
    sat::literal_vector lambda, backbones;
    for (unsigned i = 1; i < m.size(); i++) {
        lambda.push_back(sat::literal(i, m[i] == l_false));
    }
    while (!lambda.empty()) {
        IF_VERBOSE(1, verbose_stream() << "(sat-backbone-core " << lambda.size() << " " << backbones.size() << ")\n";);
        unsigned k = std::min(K, lambda.size());
        sat::literal_vector gamma, omegaN;
        for (unsigned i = 0; i < k; ++i) {
            sat::literal l = lambda[lambda.size() - i - 1];
            gamma.push_back(l);
            omegaN.push_back(~l);
        }
        while (true) {
            r = s.check(omegaN.size(), omegaN.c_ptr());
            if (r == l_true) {
                IF_VERBOSE(1, verbose_stream() << "(sat) " << omegaN << "\n";);
                prune_unfixed(lambda, s.get_model());
                break;
            }
            sat::literal_vector const& core = s.get_core();
            sat::literal_vector occurs;
            IF_VERBOSE(1, verbose_stream() << "(core " << core.size() << ")\n";);
            for (unsigned i = 0; i < omegaN.size(); ++i) {
                if (core.contains(omegaN[i])) {
                    occurs.push_back(omegaN[i]);
                }
            }
            if (occurs.size() == 1) {
                sat::literal lit = occurs.back();
                sat::literal nlit = ~lit;
                backbones.push_back(~lit);
                back_remove(lambda, ~lit);
                back_remove(gamma, ~lit);
                s.mk_clause(1, &nlit);
            }
            for (unsigned i = 0; i < omegaN.size(); ++i) {
                if (occurs.contains(omegaN[i])) {
                    omegaN[i] = omegaN.back();
                    omegaN.pop_back();
                    --i;
                }
            }
            if (omegaN.empty() && occurs.size() > 1) {
                brute_force_consequences(s, gamma, backbones);
                for (unsigned i = 0; i < gamma.size(); ++i) {
                    back_remove(lambda, gamma[i]);
                }
                break;
            }
        }
    }
    for (unsigned i = 0; i < backbones.size(); ++i) {
        sat::literal_vector cons;
        cons.push_back(backbones[i]);
        conseq.push_back(cons);
    }
    return l_true;
}


static void cnf_backbones(bool use_chunk, char const* file_name) {
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
    lbool r;
    if (use_chunk) {
        r = core_chunking(solver, vars, conseq, 100);
    }
    else {
        r = solver.get_consequences(assumptions, vars, conseq);
    }
    std::cout << vars.size() << " " << conseq.size() << "\n";
    display_status(r);
    display_statistics();
}

void tst_cnf_backbones(char ** argv, int argc, int& i) {
    if (i + 1 < argc) {
        bool use_chunk = (i + 2 < argc && argv[i + 2] == std::string("chunk"));
        cnf_backbones(use_chunk, argv[i + 1]);
        ++i;
        if (use_chunk) ++i;
    }
}
