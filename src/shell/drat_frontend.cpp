/*++
Copyright (c) 2020 Microsoft Corporation

--*/

#include<iostream>
#include<fstream>
#include "util/memory_manager.h"
#include "util/statistics.h"
#include "ast/proofs/proof_checker.h"
#include "ast/reg_decl_plugins.h"
#include "sat/dimacs.h"
#include "sat/sat_solver.h"
#include "sat/sat_drat.h"
#include "shell/drat_frontend.h"


class drup_checker {
    sat::drat& m_drat;
    sat::literal_vector m_units;

    void add_units() {
        auto const& units = m_drat.units();
        for (unsigned i = m_units.size(); i < units.size(); ++i)
            m_units.push_back(units[i].first);
    }

    void check_assertion_redundant(sat::literal_vector const& input) {
    }


    /**
    * Validate a lemma using the following attempts:
    * 1. check if it is propositional DRUP
    * 2. establish the negation of literals is unsat using a limited unfolding.
    * 3. check that it is DRUP modulo theories by taking propositional implicants from DRUP validation
    */
    sat::literal_vector drup_units;

    void check_clause(sat::literal_vector const& lits) {        
    }

    void check_drup(sat::literal_vector const& lits) {        
        add_units();
        drup_units.reset();
        if (m_drat.is_drup(lits.size(), lits.data(), drup_units)) {
            std::cout << "drup\n";
            return;
        }
        std::cout << "did not verify " << lits << "\n";
        exit(0);
    }

public:
    drup_checker(sat::drat& drat): m_drat(drat) {}

    void add(sat::literal_vector const& lits, sat::status const& st) {
        for (sat::literal lit : lits)
            while (lit.var() >= m_drat.get_solver().num_vars())
                m_drat.get_solver().mk_var(true);
        if (st.is_sat())
            check_drup(lits);
        m_drat.add(lits, st);
    }
};

unsigned read_drat(char const* drat_file) {
    ast_manager m;
    reg_decl_plugins(m);
    std::ifstream ins(drat_file);
    dimacs::drat_parser drat(ins, std::cerr);
    
    std::function<int(char const* r)> read_theory = [&](char const* r) {
        return m.mk_family_id(symbol(r));
    };
    std::function<symbol(int)> write_theory = [&](int th) {
        return m.get_family_name(th);
    };
    drat.set_read_theory(read_theory);
    params_ref p;
    reslimit lim;
    sat::solver solver(p, lim);
    sat::drat drat_checker(solver);
    drup_checker checker(drat_checker);

    for (auto const& r : drat) {
        std::cout << dimacs::drat_pp(r, write_theory); 
        std::cout.flush();
        checker.add(r.m_lits, r.m_status);
        if (drat_checker.inconsistent()) {
            std::cout << "inconsistent\n";
            return 0;
        }     
        statistics st;
        drat_checker.collect_statistics(st);
        std::cout << st << "\n";
    }
    return 0;
}
