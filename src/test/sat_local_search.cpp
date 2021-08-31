#include "sat/sat_local_search.h"
#include "sat/sat_solver.h"
#include "util/cancel_eh.h"
#include "util/scoped_ctrl_c.h"
#include "util/scoped_timer.h"

static bool build_instance(char const * filename, sat::solver& s, sat::local_search& local_search)
{
    char  line[16383];
    // for temporary storage

    std::ifstream infile(filename);
    //if (infile == NULL) //linux
    if (!infile) {
        std::cout << "File not found " << filename << "\n";
        return false;
    }
    infile.getline(line, 16383);
#ifdef _WINDOWS
    int cur_term;
    int num_vars = 0, num_constraints = 0;
    sscanf_s(line, "%d %d", &num_vars, &num_constraints);
    //std::cout << "number of variables: " << num_vars << '\n';
    //std::cout << "number of constraints: " << num_constraints << '\n';


    unsigned_vector coefficients;
    sat::literal_vector lits;

    // process objective function:
    // read coefficients
    infile >> cur_term;
    while (cur_term != 0) {
        coefficients.push_back(cur_term);
        infile >> cur_term;
    }

    // read variables
    infile >> cur_term;
    while (cur_term != 0) {
        lits.push_back(sat::literal(abs(cur_term), cur_term < 0));
        infile >> cur_term;
    }

    if (lits.size() != coefficients.size()) {
        std::cout << "Objective function format error. They have different lengths.\n";
        return false;
    }
    
    // read the constraints, one at a time
    int k;
    for (int c = 0; c < num_constraints; ++c) {        
        lits.reset();
        infile >> cur_term;
        while (cur_term != 0) {
            lits.push_back(sat::literal(abs(cur_term), cur_term > 0));
            infile >> cur_term;
        }
        infile >> k;
        //local_search.add_cardinality(lits.size(), lits.c_ptr(), static_cast<unsigned>(lits.size() - k));
        local_search.add_cardinality(lits.size(), lits.data(), static_cast<unsigned>(k));
    }

    infile.close();
    return true;
#else
    return false;
#endif
}

void tst_sat_local_search(char ** argv, int argc, int& i) {
    if (argc < i + 2) {
        std::cout << "require dimacs file name\n";
        return;
    }
    reslimit limit;
    params_ref params;
    sat::solver solver(params, limit);
    sat::local_search local_search;

    local_search.import(solver, true);
    char const* file_name = argv[i + 1];
    ++i;

    int cutoff_time = 1;

    int v;
    while (i + 1 < argc) {
        std::cout << argv[i + 1] << "\n";
        // set other ad hoc parameters.
        if (argv[i + 1][0] == '-' && i + 2 < argc) {
            switch (argv[i + 1][1]) {
            case 's': // seed
                v = atoi(argv[i + 2]);
                local_search.config().set_random_seed(v);
                break;
            case 't': // cutoff_time
                v = atoi(argv[i + 2]);
                cutoff_time = v;
                break;
            case 'b': // best_known_value
                v = atoi(argv[i + 2]);
                local_search.config().set_best_known_value(v);
                break;
            default:
                ++i;
                v = -1;
                break;
            }
        }
        ++i;
    }

    if (!build_instance(file_name, solver, local_search)) {
        return;
    }

    //std::cout << "local instance built\n";


    // set up cancellation/timeout environment.

    cancel_eh<reslimit> eh(local_search.rlimit());
    scoped_ctrl_c ctrlc(eh, false, true);
    scoped_timer timer(cutoff_time*1000, &eh);        
    local_search.check(0, nullptr, nullptr);    

}
