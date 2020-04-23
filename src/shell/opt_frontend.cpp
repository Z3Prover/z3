
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

#include<fstream>
#include<signal.h>
#include<time.h>
#include "util/gparams.h"
#include "util/timeout.h"
#include "util/cancel_eh.h"
#include "util/scoped_timer.h"
#include "ast/ast_util.h"
#include "ast/arith_decl_plugin.h"
#include "ast/ast_pp.h"
#include "ast/reg_decl_plugins.h"
#include "model/model_smt2_pp.h"
#include "opt/opt_context.h"
#include "shell/opt_frontend.h"
#include "opt/opt_parse.h"

extern bool g_display_statistics;
static bool g_first_interrupt = true;
static opt::context* g_opt = nullptr;
static double g_start_time = 0;
static unsigned_vector g_handles;
static std::mutex *display_stats_mux = new std::mutex;


static void display_results() {
    IF_VERBOSE(1, 
               if (g_opt) {
                   model_ref mdl;
                   g_opt->get_model(mdl);
                   if (mdl) {
                       model_smt2_pp(verbose_stream(), g_opt->get_manager(), *mdl, 0); 
                   }
                   for (unsigned h : g_handles) {
                       expr_ref lo = g_opt->get_lower(h);
                       expr_ref hi = g_opt->get_upper(h);
                       if (lo == hi) {
                           std::cout << "   " << lo << "\n";
                       }
                       else {
                           std::cout << "  [" << lo << ":" << hi << "]\n";
                       }
                   }
               });
}

static void display_statistics() {
    std::lock_guard<std::mutex> lock(*display_stats_mux);
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
        display_statistics();
        raise(SIGINT);
    }
}

static void on_timeout() {
    display_statistics();
    exit(0);
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
        cancel_eh<reslimit> eh(m.limit());
        unsigned timeout = std::stoul(gparams::get_value("timeout"));
        unsigned rlimit = std::stoi(gparams::get_value("rlimit"));
        scoped_timer timer(timeout, &eh);
        scoped_rlimit _rlimit(m.limit(), rlimit);
        expr_ref_vector asms(m);
        lbool r = opt.optimize(asms);
        switch (r) {
        case l_true:  std::cout << "sat\n"; break;
        case l_false: std::cout << "unsat\n"; break;
        case l_undef: std::cout << "unknown\n"; break;
        }
        
        if (r != l_false && gparams::get_ref().get_bool("model_validate", false)) {
            model_ref mdl;
            opt.get_model(mdl);
            expr_ref_vector hard(m);
            opt.get_hard_constraints(hard);
            for (expr* h : hard) {
                if (!mdl->is_true(h)) {
                    std::cout << mk_pp(h, m) << " evaluates to: " << (*mdl)(h) << "\n";
                }
            }
        }
    }
    catch (z3_exception & ex) {
        std::cerr << ex.msg() << "\n";
    }
    display_statistics();
    g_opt = nullptr;
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

