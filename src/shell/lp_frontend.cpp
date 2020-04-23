/*++
Copyright (c) 2016 Microsoft Corporation

Author:

    Lev Nachmanson 2016-10-27

--*/

#include "math/lp/lp_settings.h"
#include "math/lp/mps_reader.h"
#include "util/timeout.h"
#include "util/cancel_eh.h"
#include "util/scoped_timer.h"
#include "util/rlimit.h"
#include "util/gparams.h"
#include <signal.h>
#include "smt/params/smt_params_helper.hpp"

namespace {
static std::mutex *display_stats_mux = new std::mutex;

static lp::lp_solver<double, double>* g_solver = nullptr;

static void display_statistics() {
    std::lock_guard<std::mutex> lock(*display_stats_mux);
    if (g_solver && g_solver->settings().print_statistics) {
        // TBD display relevant information about statistics
    }
}

static void STD_CALL on_ctrl_c(int) {
    signal (SIGINT, SIG_DFL);
    display_statistics();
    raise(SIGINT);
}

static void on_timeout() {
    display_statistics();
    exit(0);    
}

struct front_end_resource_limit : public lp::lp_resource_limit {
    reslimit& m_reslim;

    front_end_resource_limit(reslimit& lim):
        m_reslim(lim)
    {}

    bool get_cancel_flag() override { return !m_reslim.inc(); }
};

void run_solver(smt_params_helper & params, char const * mps_file_name) {

    reslimit rlim;
    unsigned timeout = gparams::get_ref().get_uint("timeout", 0);
    unsigned rlimit  = gparams::get_ref().get_uint("rlimit", 0);
    front_end_resource_limit lp_limit(rlim);

    scoped_rlimit _rlimit(rlim, rlimit);
    cancel_eh<reslimit> eh(rlim);
    scoped_timer timer(timeout, &eh);

    std::string fn(mps_file_name);
    lp::mps_reader<double, double> reader(fn);
    reader.set_message_stream(&std::cout); // can be redirected
    reader.read();
    if (!reader.is_ok()) {
        std::cerr << "cannot process " << mps_file_name << std::endl;
        return;
    }
    lp::lp_solver<double, double> * solver =  reader.create_solver(false);  // false - to create the primal solver
    solver->settings().set_resource_limit(lp_limit);
    g_solver = solver;
    if (params.arith_min()) {
        solver->flip_costs();
    }
    solver->settings().set_message_ostream(&std::cout);
    solver->settings().report_frequency = params.arith_rep_freq();
    solver->settings().print_statistics = params.arith_print_stats();
    solver->settings().simplex_strategy() = lp:: simplex_strategy_enum::lu;

    solver->find_maximal_solution();

    *(solver->settings().get_message_ostream()) << "status is " << lp_status_to_string(solver->get_status()) << std::endl;
    if (solver->get_status() == lp::lp_status::OPTIMAL) {
        if (params.arith_min()) {
            solver->flip_costs();
        }
        solver->print_model(std::cout);
    }

    display_statistics();
    g_solver = nullptr;
    delete solver;
}
}

unsigned read_mps_file(char const * mps_file_name) {
    signal(SIGINT, on_ctrl_c);
    register_on_timeout_proc(on_timeout);
    smt_params_helper p;
    param_descrs r;
    p.collect_param_descrs(r);
    run_solver(p, mps_file_name);
    return 0;
}
