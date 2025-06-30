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
#include "util/mutex.h"
#include "parsers/smt2/smt2parser.h"
#include "smt/smt_context.h"
#include "muz/fp/dl_cmds.h"
#include "cmd_context/extra_cmds/dbg_cmds.h"
#include "cmd_context/extra_cmds/proof_cmds.h"
#include "opt/opt_cmds.h"
#include "cmd_context/extra_cmds/polynomial_cmds.h"
#include "cmd_context/extra_cmds/subpaving_cmds.h"
#include "smt/smt2_extra_cmds.h"
#include "smt/smt_solver.h"

static mutex *display_stats_mux = new mutex;

extern bool g_display_statistics;
extern bool g_display_model;
static clock_t             g_start_time;
static cmd_context *       g_cmd_context = nullptr;
static smt::context *      g_smt_context = nullptr;  // Track active SMT context for timeout stats

static void display_statistics() {
    lock_guard lock(*display_stats_mux);
    clock_t end_time = clock();
    if (g_cmd_context && g_display_statistics) {
        if (g_cmd_context) {
            g_cmd_context->set_regular_stream("stdout");
            g_cmd_context->display_statistics(true, ((static_cast<double>(end_time) - static_cast<double>(g_start_time)) / CLOCKS_PER_SEC));
        }
        std::cout.flush();
        std::cerr.flush();
    }
}

static void display_model() {
    if (g_display_model && g_cmd_context) {
        model_ref mdl;
        if (g_cmd_context->is_model_available(mdl))
            g_cmd_context->display_model(mdl);
    }
}

static void on_timeout() {
    // Force aggregation of theory statistics before displaying them
    std::cout << "[DEBUG] on_timeout() called - forcing statistics aggregation\n";
    
    if (g_cmd_context) {
        std::cout << "[DEBUG] Calling g_cmd_context->flush_statistics()\n";
        g_cmd_context->flush_statistics();
    }
    
    // Try to access the SMT context directly if available
    if (g_smt_context) {
        std::cout << "[DEBUG] Found g_smt_context! Calling flush_statistics() directly\n";
        g_smt_context->flush_statistics();
        
        // Also collect the aggregated stats into the cmd_context singleton
        if (g_cmd_context) {
            std::cout << "[DEBUG] Collecting SMT context stats into cmd_context singleton\n";
            g_cmd_context->collect_smt_statistics(*g_smt_context);
        }
    } else {
        std::cout << "[DEBUG] g_smt_context is null\n";
    }
    
    display_statistics();
    _Exit(0);
}

static void STD_CALL on_ctrl_c(int) {
    signal (SIGINT, SIG_DFL);
    display_statistics();
    raise(SIGINT);
}

// Functions to register/unregister the active SMT context for timeout handling
void register_smt_context(smt::context* ctx) {
    g_smt_context = ctx;
    std::cout << "[DEBUG] Registered SMT context: " << (void*)ctx << "\n";
}

void unregister_smt_context() {
    std::cout << "[DEBUG] Unregistered SMT context: " << (void*)g_smt_context << "\n";
    g_smt_context = nullptr;
}

void help_tactics() {
    struct cmp {
        bool operator()(tactic_cmd* a, tactic_cmd* b) const {
            return a->get_name().str() < b->get_name().str();
        }
    };
    cmd_context ctx;
    ptr_vector<tactic_cmd> cmds;
    for (auto cmd : ctx.tactics()) 
        cmds.push_back(cmd);
    cmp lt;
    std::sort(cmds.begin(), cmds.end(), lt);
    for (auto cmd : cmds) 
        std::cout << "- " << cmd->get_name() << " " << cmd->get_descr() << "\n";
}

void help_simplifiers() {
    struct cmp {
        bool operator()(simplifier_cmd* a, simplifier_cmd* b) const {
            return a->get_name().str() < b->get_name().str();
        }
    };
    cmd_context ctx;
    ptr_vector<simplifier_cmd> cmds;
    for (auto cmd : ctx.simplifiers()) 
        cmds.push_back(cmd);
    cmp lt;
    std::sort(cmds.begin(), cmds.end(), lt);
    for (auto cmd : cmds) 
        std::cout << "- " << cmd->get_name() << " " << cmd->get_descr() << "\n";
}

void help_tactic(char const* name, bool markdown) {
    cmd_context ctx;
    for (auto cmd : ctx.tactics()) {
        if (cmd->get_name() == name) {
            tactic_ref t = cmd->mk(ctx.m());
            param_descrs descrs;
            t->collect_param_descrs(descrs);
            if (markdown)
                descrs.display_markdown(std::cout);
            else
                descrs.display(std::cout, 4);
        }
    }
}

void help_simplifier(char const* name, bool markdown) {
    cmd_context ctx;
    for (auto cmd : ctx.simplifiers()) {
        if (cmd->get_name() == name) {
            auto fac = cmd->factory();
            param_descrs descrs;
            ast_manager& m = ctx.m();
            default_dependent_expr_state st(m);
            params_ref p;
            scoped_ptr<dependent_expr_simplifier> s = fac(m, p, st);
            s->collect_param_descrs(descrs);
            if (markdown)
                descrs.display_markdown(std::cout);
            else
                descrs.display(std::cout, 4);
        }
    }
}

void help_probes() {
    struct cmp {
        bool operator()(probe_info* a, probe_info* b) const {
            return a->get_name().str() < b->get_name().str();
        }
    };
    cmd_context ctx;
    ptr_vector<probe_info> cmds;
    for (auto cmd : ctx.probes()) 
        cmds.push_back(cmd);
    cmp lt;
    std::sort(cmds.begin(), cmds.end(), lt);
    for (auto cmd : cmds) 
        std::cout << "- " << cmd->get_name() << " " << cmd->get_descr() << "\n";
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
    install_proof_cmds(ctx);

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

    display_statistics();
    display_model();
    g_cmd_context = nullptr;
    return result ? 0 : 1;
}

