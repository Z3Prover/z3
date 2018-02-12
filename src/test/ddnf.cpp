/*++
Copyright (c) 2015 Microsoft Corporation

--*/

#include "muz/ddnf/ddnf.h"
#include "muz/rel/tbv.h"
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

static char const* g_file = nullptr;


void create_forwarding(
    char const* file, 
    datalog::ddnf_core& ddnf, 
    ptr_vector<tbv>& tbvs,
    vector<unsigned_vector>& fwd_indices) {

    IF_VERBOSE(1, verbose_stream() << "creating (and forgetting) forwarding index\n";);
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
        fwd_indices.push_back(unsigned_vector());
        unsigned_vector& forwarding_index = fwd_indices.back();
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

    IF_VERBOSE(1, verbose_stream() << "populate ddnf\n";);

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
        IF_VERBOSE(1, verbose_stream() << K << " " << P << "\n";);
        unsigned p;
        for (unsigned g = 0; g < K; ++g) {
            is >> p;
            std::getline(is, line);
            tbv* t = tbvm.allocate(line.c_str());
            ddnf->insert(*t);
            IF_VERBOSE(2, tbvm.display(verbose_stream() << line << " ", *t) << "\n";);
            tbvs.push_back(t);
            if (p > P) {
                std::cout << "port number " << p << " too big " << P << "\n";
                tbvm.display(std::cout, *t) << " " << line << "\n";
                exit(0);
            }
            if (p == 0 && tbvm.equals(*t, *tX)) break;
            // std::cout << ddnf->well_formed() << "\n";
        }
    }

    tbvm.deallocate(tX);

    return ddnf;
}


static void read_args(char ** argv, int argc, int& i) {
    if (argc == i + 2) {
        g_file = argv[i + 1];
        ++i;
        return;
    }

    if (!g_file) {
        std::cout << "Need routing table file as argument. Arguments provided: ";
        for (int j = i; j < argc; ++j) {
            std::cout << argv[j] << " ";
        }
        std::cout << "\n";
        exit(0);
    }

}

typedef std::pair<unsigned, unsigned> u_pair;

struct uu_eq { bool operator()(u_pair u1, u_pair u2) const { return u1 == u2; } };

typedef map<u_pair, unsigned, pair_hash<unsigned_hash, unsigned_hash>, uu_eq > pair_table;

static unsigned refine_forwarding(
    unsigned_vector& p,
    unsigned_vector const& q) {
    unsigned sz = p.size();
    unsigned n = 0, m = 0;
    pair_table tbl;
    for (unsigned i = 0; i < sz; ++i) {
        u_pair pr = std::make_pair(p[i], q[i]);
        if (tbl.find(pr, m)) {
            p[i] = m;
        }
        else {
            p[i] = n;
            tbl.insert(pr, n++);
        }
    }    
    return n;
}

static void refine_forwarding(
    datalog::ddnf_core& ddnf,
    vector<unsigned_vector> const& fwd_indices) {
    unsigned_vector roots;
    roots.resize(ddnf.size());
    for (unsigned i = 0; i < roots.size(); ++i) {
        roots[i] = 0;
    }
    unsigned max_class = 1;
    for (unsigned i = 0; i < fwd_indices.size(); ++i) {
        unsigned_vector const& fwd = fwd_indices[i];
        max_class = refine_forwarding(roots, fwd);
    }    
    std::cout << "num classes: " << max_class << "\n";    
}

void tst_ddnf(char ** argv, int argc, int& i) {
    read_args(argv, argc, i);
    ptr_vector<tbv> tbvs;
    datalog::ddnf_core* ddnf = populate_ddnf(g_file, tbvs);
    IF_VERBOSE(1, ddnf->display(verbose_stream()););
    vector<unsigned_vector> fwd_indices;
    create_forwarding(g_file, *ddnf, tbvs, fwd_indices);
    refine_forwarding(*ddnf, fwd_indices);
    std::cout << "resulting size: " << ddnf->size() << "\n";
    ddnf->display_statistics(std::cout);
    IF_VERBOSE(1, ddnf->display(verbose_stream());
               verbose_stream() << ddnf->well_formed() << "\n";);
    
    tbv_manager& tbvm = ddnf->get_tbv_manager();
    for (unsigned i = 0; i < tbvs.size(); ++i) {
        tbvm.deallocate(tbvs[i]);
    }
    dealloc(ddnf);
}

void tst_ddnf1() {
    enable_trace("ddnf");
    unsigned W = 2;
    datalog::ddnf_core ddnf(W);
    tbv_manager& tbvm = ddnf.get_tbv_manager();
    tbv* tXX = tbvm.allocate("xx");
    tbv* t1X = tbvm.allocate("1x");
    tbv* tX1 = tbvm.allocate("x1");
    tbv* t11 = tbvm.allocate("11");
    ddnf.insert(*tXX);
    ddnf.insert(*t11);
    ddnf.insert(*tX1);
    ddnf.insert(*t1X); 
    ddnf.display(std::cout);
    tbvm.deallocate(tXX);
    tbvm.deallocate(t1X);
    tbvm.deallocate(tX1);
    tbvm.deallocate(t11);
}


