#include "ddnf.h"
#include "tbv.h"
#include <iostream>
#include <fstream>
#include <list>
#include <vector>
#include <string>
#include <cstring>
#include <cstdlib>
#include <map>

/*
TBD: count number of nodes, number of operations accross all insertions
*/

void read_nums(std::istream& is, unsigned & x, unsigned& y) {
    x = 0; y = 0;
    is >> x;
    is >> y;
    std::string line;
    std::getline(is, line);
}

static bool g_verbose = false;
static char const* g_file = 0;


void create_forwarding(char const* file, datalog::ddnf_core& ddnf, ptr_vector<tbv>& tbvs) {

    if (g_verbose) {
        std::cout << "creating (and forgetting) forwarding index\n";
    }
    std::ifstream is(file);
    if (is.bad() || is.fail()) {
        std::cout << "could not load " << file << "\n";
        exit(0);
    }

    std::string line;
    unsigned W, M;
    read_nums(is, W, M);
    tbv_manager& tbvm = ddnf.get_tbv_manager();
    tbv* tX = tbvm.allocateX();
    unsigned_vector forwarding_set;
    for (unsigned r = 0; r < M; ++r) {
        unsigned P, K;
        read_nums(is, K, P);
        ddnf.reset_accumulate();
        unsigned p;
        unsigned_vector forwarding_index;
        forwarding_index.resize(ddnf.size());
        for (unsigned g = 0; g < K; ++g) {
            is >> p;
            std::getline(is, line);
            tbv* t = tbvm.allocate(line.c_str());
            if (p > P) {
                std::cout << "port number " << p << " too big " << P << "\n";
                tbvm.display(std::cout, *t) << " " << line << "\n";
                exit(0);
            }
            forwarding_set.reset();
            ddnf.accumulate(*t, forwarding_set);
            for (unsigned i = 0; i < forwarding_set.size(); ++i) {
                forwarding_index[forwarding_set[i]] = p;
            }
            tbvs.push_back(t);
            if (p == 0 && tbvm.equals(*t, *tX)) break;
        }
    }
    tbvm.deallocate(tX);
}

datalog::ddnf_core* populate_ddnf(char const* file, ptr_vector<tbv>& tbvs) {

    if (g_verbose) {
        std::cout << "populate ddnf\n";
    }

    std::ifstream is(file);
    if (is.bad() || is.fail()) {
        std::cout << "could not load " << file << "\n";
        exit(0);
    }

    std::string line;
    unsigned W, M;
    read_nums(is, W, M);
    datalog::ddnf_core* ddnf = alloc(datalog::ddnf_core, W);
    tbv_manager& tbvm = ddnf->get_tbv_manager();
    tbv* tX = tbvm.allocateX();
    for (unsigned r = 0; r < M; ++r) {
        unsigned P, K;
        read_nums(is, K, P);
        if (g_verbose) {
            std::cout << K << " " << P << "\n";
        }
        unsigned p;
        for (unsigned g = 0; g < K; ++g) {
            is >> p;
            std::getline(is, line);
            tbv* t = tbvm.allocate(line.c_str());
            ddnf->insert(*t);
            //tbvm.display(std::cout << line << " ", *t) << "\n";
            tbvs.push_back(t);
            if (p > P) {
                std::cout << "port number " << p << " too big " << P << "\n";
                tbvm.display(std::cout, *t) << " " << line << "\n";
                exit(0);
            }
            if (p == 0 && tbvm.equals(*t, *tX)) break;
        }
    }

    tbvm.deallocate(tX);

    return ddnf;
}


static void read_args(char ** argv, int argc) {
    if (argc == 3) {
        g_file = argv[2];
        return;
    }

    for (int i = 2; i < argc; ++i) {
        if (argv[i] == "v") {
            g_verbose = true;            
        }
        else {
            g_file = argv[i];
        }
    }

    if (!g_file) {
        std::cout << "Need routing table file as argument. Arguments provided: ";
        for (int i = 0; i < argc; ++i) {
            std::cout << argv[i] << " ";
        }
        std::cout << "\n";
        exit(0);
    }

}

void tst_ddnf(char ** argv, int argc, int& i) {
    read_args(argv, argc);
    ptr_vector<tbv> tbvs;
    datalog::ddnf_core* ddnf = populate_ddnf(g_file, tbvs);
    create_forwarding(g_file, *ddnf, tbvs);
    std::cout << "resulting size: " << ddnf->size() << "\n";
    ddnf->display_statistics(std::cout);
    if (g_verbose) {
        ddnf->display(std::cout);
    }
    std::cout.flush();

    tbv_manager& tbvm = ddnf->get_tbv_manager();
    for (unsigned i = 0; i < tbvs.size(); ++i) {
        tbvm.deallocate(tbvs[i]);
    }
    dealloc(ddnf);
}




