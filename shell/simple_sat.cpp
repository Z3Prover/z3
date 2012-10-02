/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    simple_sat.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2006-10-10.

Revision History:

--*/
#include<fstream>
#include<time.h>
#include"front_end_params.h"
#include"sat_def.h"
#include"dimacs_parser.h"
#include"timeit.h"
#include"mem_stat.h"

class simple_sat_solver : public no_extension {
    const front_end_params &         m_params;
    sat_solver<simple_sat_solver> *  m_sat;
    unsigned                         m_num_vars;
    svector<lbool>                   m_model;
public:
    simple_sat_solver(const front_end_params & p):
        m_params(p),
        m_sat(new sat_solver<simple_sat_solver>(*this, p)),
        m_num_vars(0) {
    }

    ~simple_sat_solver() {
        delete m_sat;
    }

    static bool enable_ref_counters() {
        return false; 
    }

    void mk_var() {
	m_sat->mk_var();
	m_num_vars++;
    }

    void mk_clause(const literal_vector & lits) {
	m_sat->mk_main_clause(lits);
    }

    unsigned get_num_vars() const {
	return m_num_vars;
    }

    lbool check() {
	return m_sat->check();
    }
    
    void mk_model() {
        if (m_params.m_build_model) {
            m_sat->save_assignment(m_model);
        }
    }

    void display_model(std::ostream & out) const {
        int sz = m_model.size();
        for (int i = 1; i < sz; i++) {
            if (m_model[i] == l_true) {
                out << i << " ";
            }
            else if (m_model[i] == l_false) {
                out << -i << " ";
            }
        }
        out << "\n";
    }

    void display_statistics(std::ostream & out) const {
	m_sat->display_statistics(out);
    }
};

extern bool g_display_statistics;
extern front_end_params g_front_end_params;

void solve_cnf(const char * file) {
    clock_t start_time = clock();
    simple_sat_solver solver(g_front_end_params);
    std::ifstream in(file);
    parse_dimacs(in, solver);
    lbool r = solver.check();
    clock_t end_time   = clock();
    switch(r) {
    case l_false:
        std::cout << "unsat\n";
	break;
    case l_undef:
	std::cout << "unknown\n";
	break;
    case l_true:
	std::cout << "sat\n";
        if (g_front_end_params.m_build_model) {
            solver.display_model(std::cout);
        }
	break;
    }
    if (g_display_statistics) {
	solver.display_statistics(std::cerr);
        memory::display_max_usage(std::cerr);
        std::cerr << "time:               " << ((static_cast<double>(end_time) - static_cast<double>(start_time)) / CLOCKS_PER_SEC) << "\n";
    }
}

