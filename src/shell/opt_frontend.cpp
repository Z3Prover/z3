
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

#include<fstream>
#include<signal.h>
#include<time.h>
#include "opt/opt_context.h"
#include "ast/ast_util.h"
#include "ast/arith_decl_plugin.h"
#include "ast/ast_pp.h"
#include "util/gparams.h"
#include "util/timeout.h"
#include "ast/reg_decl_plugins.h"
#include "opt/opt_parse.h"
#include "shell/opt_frontend.h"

extern bool g_display_statistics;
static bool g_first_interrupt = true;
static opt::context* g_opt = 0;
static double g_start_time = 0;
static unsigned_vector g_handles;



static void display_results() {
    if (g_opt) {
        for (unsigned i = 0; i < g_handles.size(); ++i) {
            expr_ref lo = g_opt->get_lower(g_handles[i]);
            expr_ref hi = g_opt->get_upper(g_handles[i]);
            if (lo == hi) {
                std::cout << "   " << lo << "\n";
            }
            else {
                std::cout << "  [" << lo << ":" << hi << "]\n";
            }
        }
    }
}

static void display_statistics() {
    if (g_display_statistics && g_opt) {
        ::statistics stats;
        g_opt->collect_statistics(stats);
        stats.display(std::cout);
        double end_time = static_cast<double>(clock());
        std::cout << "time:                " << (end_time - g_start_time)/CLOCKS_PER_SEC << " secs\n";
    }    

    display_results();
}

static void STD_CALL on_ctrl_c(int) {
    if (g_opt && g_first_interrupt) {
        g_opt->get_manager().limit().cancel();
        g_first_interrupt = false;
    }
    else {
        signal (SIGINT, SIG_DFL);
        #pragma omp critical (g_display_stats) 
        {
            display_statistics();
        }
        raise(SIGINT);
    }
}

static void on_timeout() {
    #pragma omp critical (g_display_stats) 
    {
        display_statistics();
        exit(0);
    }
}

static unsigned parse_opt(std::istream& in, opt_format f) {
    ast_manager m;
    reg_decl_plugins(m);
    opt::context opt(m);
    g_opt = &opt;
    params_ref p = gparams::get_module("opt");
    opt.updt_params(p);
    switch (f) {
    case wcnf_t:
        parse_wcnf(opt, in, g_handles);
        break;
    case opb_t:
        parse_opb(opt, in, g_handles);
        break;
    case lp_t:
        parse_lp(opt, in, g_handles);
        break;
    }
    try {
        lbool r = opt.optimize();
        switch (r) {
        case l_true:  std::cout << "sat\n"; break;
        case l_false: std::cout << "unsat\n"; break;
        case l_undef: std::cout << "unknown\n"; break;
        }
        
        if (r != l_false && gparams::get().get_bool("model_validate", false)) {
            model_ref mdl;
            opt.get_model(mdl);
            expr_ref_vector hard(m);
            opt.get_hard_constraints(hard);
            for (expr* h : hard) {
                expr_ref tmp(m);
                VERIFY(mdl->eval(h, tmp));
                if (!m.is_true(tmp)) {
                    std::cout << mk_pp(h, m) << " " << tmp << "\n";
                }
            }
        }
    }
    catch (z3_exception & ex) {
        std::cerr << ex.msg() << "\n";
    }
    #pragma omp critical (g_display_stats) 
    {
        display_statistics();
        register_on_timeout_proc(0);
        g_opt = 0;
    }    
    return 0;
}

unsigned parse_opt(char const* file_name, opt_format f) {
    g_first_interrupt = true;
    g_start_time = static_cast<double>(clock());
    register_on_timeout_proc(on_timeout);
    signal(SIGINT, on_ctrl_c);
    if (file_name) {
        std::ifstream in(file_name);
        if (in.bad() || in.fail()) {
            std::cerr << "(error \"failed to open file '" << file_name << "'\")" << std::endl;
            exit(ERR_OPEN_FILE);
        }
        return parse_opt(in, f);
    }
    else {
        return parse_opt(std::cin, f);
    }
}

