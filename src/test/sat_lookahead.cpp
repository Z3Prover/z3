#include "sat/sat_solver.h"
#include "sat/sat_watched.h"
#include "util/statistics.h"
#include "sat/sat_lookahead.h"
#include "sat/dimacs.h"

static void display_model(sat::model const & m) {
    for (unsigned i = 1; i < m.size(); i++) {
        switch (m[i]) {
        case l_false: std::cout << "-" << i << " ";  break;
        case l_undef: break;
        case l_true: std::cout << i << " ";  break;
        }
    }
    std::cout << "\n";
}


void tst_sat_lookahead(char ** argv, int argc, int& i) {
    if (argc != i + 2) {
        std::cout << "require dimacs file name\n";
        return;
    }
//    enable_trace("sat");
    reslimit limit;
    params_ref params;
    sat::solver solver(params, limit);
    char const* file_name = argv[i + 1];
    ++i;

    {
        std::ifstream in(file_name);
        if (in.bad() || in.fail()) {
            std::cerr << "(error \"failed to open file '" << file_name << "'\")" << std::endl;
            exit(ERR_OPEN_FILE);
        }
        parse_dimacs(in, solver);
    }
   
    sat::lookahead lh(solver);

    IF_VERBOSE(20, solver.display_status(verbose_stream()););

    lbool is_sat = lh.check();
    std::cout << is_sat << "\n";

    statistics st;
    lh.collect_statistics(st);
    st.display(std::cout);
    if (is_sat == l_true) {
        display_model(lh.get_model());
    }
}
