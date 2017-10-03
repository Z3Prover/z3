/*++
Copyright (c) 2016 Microsoft Corporation

Author:

    Lev Nachmanson 2016-10-27

--*/

#include "util/lp/lp_params.hpp"
#include "util/lp/lp_settings.h"
#include "util/lp/mps_reader.h"
#include "util/timeout.h"
#include "util/cancel_eh.h"
#include "util/scoped_timer.h"
#include "util/rlimit.h"
#include "util/gparams.h"
#include <signal.h>

static lp::lp_solver<double, double>* g_solver = nullptr;

static void display_statistics() {
    if (g_solver && g_solver->settings().print_statistics) {
        // TBD display relevant information about statistics
    }
}

static void STD_CALL on_ctrl_c(int) {
    signal (SIGINT, SIG_DFL);
    #pragma omp critical (g_display_stats)
    {
        display_statistics();
    }
    raise(SIGINT);
}

static void on_timeout() {
    #pragma omp critical (g_display_stats)
    {
        display_statistics();
        exit(0);
    }
}

struct front_end_resource_limit : public lp::lp_resource_limit {
    reslimit& m_reslim;

    front_end_resource_limit(reslimit& lim):
        m_reslim(lim)
    {}

    bool get_cancel_flag() override { return !m_reslim.inc(); }
};

void run_solver(lp_params & params, char const * mps_file_name) {

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
    if (params.min()) {
        solver->flip_costs();
    }
    solver->settings().set_message_ostream(&std::cout);
    solver->settings().report_frequency = params.rep_freq();
    solver->settings().print_statistics = params.print_stats();
    solver->settings().simplex_strategy() = lp:: simplex_strategy_enum::lu;

    solver->find_maximal_solution();

    *(solver->settings().get_message_ostream()) << "status is " << lp_status_to_string(solver->get_status()) << std::endl;
    if (solver->get_status() == lp::lp_status::OPTIMAL) {
        if (params.min()) {
            solver->flip_costs();
        }
        solver->print_model(std::cout);
    }

//    #pragma omp critical (g_display_stats)
    {
        display_statistics();
        register_on_timeout_proc(nullptr);
        g_solver = nullptr;
    }
    delete solver;
}

unsigned read_mps_file(char const * mps_file_name) {
    signal(SIGINT, on_ctrl_c);
    register_on_timeout_proc(on_timeout);
    lp_params p;
    param_descrs r;
    p.collect_param_descrs(r);
    run_solver(p, mps_file_name);
    return 0;
}
