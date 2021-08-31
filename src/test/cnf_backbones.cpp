/*++
Copyright (c) 2017 Microsoft Corporation

--*/
#include<iostream>
#include<time.h>
#include<signal.h>
#include "util/timeout.h"
#include "util/rlimit.h"
#include "sat/dimacs.h"
#include "sat/sat_solver.h"
#include "util/gparams.h"

static sat::solver * g_solver = nullptr;
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

#if 0
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
#endif

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

static void track_clause(sat::solver& dst,
                         sat::literal_vector& lits,
                         sat::literal_vector& assumptions,
                         vector<sat::literal_vector>& tracking_clauses) {
    sat::literal lit = sat::literal(dst.mk_var(true, false), false);
    tracking_clauses.set(lit.var(), lits);
    lits.push_back(~lit);
    dst.mk_clause(lits.size(), lits.data());
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

static void brute_force_consequences(sat::solver& s, sat::literal_vector const& asms, sat::literal_vector const& gamma, sat::literal_vector& backbones) {
    for (unsigned i = 0; i < gamma.size(); ++i) {
        sat::literal nlit = ~gamma[i];
        sat::literal_vector asms1(asms);
        asms1.push_back(nlit);
        lbool r = s.check(asms1.size(), asms1.data());
        if (r == l_false) {
            backbones.push_back(gamma[i]);
        }
    }
}

static lbool core_chunking(sat::solver& s, sat::bool_var_vector& vars, sat::literal_vector const& asms, vector<sat::literal_vector>& conseq, unsigned K) {
    lbool r = s.check(asms.size(), asms.data());
    if (r != l_true) {
        return r;
    }
    sat::model const & m = s.get_model();
    sat::literal_vector lambda, backbones;
    for (unsigned i = 0; i < vars.size(); i++) {
        lambda.push_back(sat::literal(vars[i], m[vars[i]] == l_false));
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
            sat::literal_vector asms1(asms);
            asms1.append(omegaN);
            r = s.check(asms1.size(), asms1.data());
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
                brute_force_consequences(s, asms, gamma, backbones);
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
    sat::solver solver(p, limit);
    sat::solver solver2(p, limit);
    g_solver = &solver;

    if (file_name) {
        std::ifstream in(file_name);
        if (in.bad() || in.fail()) {
            std::cerr << "(error \"failed to open file '" << file_name << "'\")" << std::endl;
            exit(ERR_OPEN_FILE);
        }
        if (!parse_dimacs(in, std::cerr, solver)) return;
    }
    else {
        if (!parse_dimacs(std::cin, std::cerr, solver)) return;
    }
    IF_VERBOSE(20, solver.display_status(verbose_stream()););
    
    vector<sat::literal_vector> conseq;
    sat::bool_var_vector vars;
    sat::literal_vector assumptions;
    unsigned num_vars = solver.num_vars();
    if (p.get_bool("dimacs.core", false)) {
        g_solver = &solver2;        
        vector<sat::literal_vector> tracking_clauses;
        track_clauses(solver, solver2, assumptions, tracking_clauses);
    }
    // remove this line to limit variables to exclude assumptions
    num_vars = g_solver->num_vars();
    for (unsigned i = 1; i < num_vars; ++i) {
        vars.push_back(i);        
        g_solver->set_external(i);
    }
    lbool r;
    if (use_chunk) {
        r = core_chunking(*g_solver, vars, assumptions, conseq, 100);
    }
    else {
        r = g_solver->get_consequences(assumptions, vars, conseq);
    }
    std::cout << vars.size() << " " << conseq.size() << "\n";
    display_status(r);
    display_statistics();
}

void tst_cnf_backbones(char ** argv, int argc, int& i) {
    bool use_chunk = i + 1 < argc && argv[i + 1] == std::string("chunk");
    if (use_chunk) ++i;     
    char const* file = "";
    if (i + 1 < argc) {
        file = argv[i + 1];
    }
    else {
        file = argv[1];
    }
    cnf_backbones(use_chunk, file);
    ++i;
}
