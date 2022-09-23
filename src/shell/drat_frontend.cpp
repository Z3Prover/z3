/*++
Copyright (c) 2020 Microsoft Corporation

--*/

#include<iostream>
#include<fstream>
#include "ast/bv_decl_plugin.h"
#include "util/memory_manager.h"
#include "util/statistics.h"
#include "sat/dimacs.h"
#include "sat/sat_solver.h"
#include "sat/sat_drat.h"
#include "smt/smt_solver.h"
#include "shell/drat_frontend.h"
#include "parsers/smt2/smt2parser.h"
#include "cmd_context/cmd_context.h"
#include "ast/proofs/proof_checker.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/reg_decl_plugins.h"
#include "sat/smt/arith_proof_checker.h"


class drup_checker {
    sat::drat& m_drat;
    sat::literal_vector m_units;
    bool m_check_inputs = false;

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


#if 0

    bool validate_hint(expr_ref_vector const& exprs, sat::literal_vector const& lits, sat::proof_hint const& hint) {
        arith_util autil(m);
        arith::proof_checker achecker(m);
        proof_checker pc(m);
        switch (hint.m_ty) {
        case sat::hint_type::null_h:
            break;
        case sat::hint_type::bound_h:
        case sat::hint_type::farkas_h: 
        case sat::hint_type::implied_eq_h: {
            achecker.reset();
            for (auto const& [a, b]: hint.m_eqs) {
                expr* x = exprs[a];
                expr* y = exprs[b];
                achecker.add_eq(x, y);
            }
            for (auto const& [a, b]: hint.m_diseqs) {
                expr* x = exprs[a];
                expr* y = exprs[b];
                achecker.add_diseq(x, y);
            }
            
            unsigned sz = hint.m_literals.size();
            for (unsigned i = 0; i < sz; ++i) {
                auto const& [coeff, lit] = hint.m_literals[i];
                app_ref e(to_app(m_b2e[lit.var()]), m);
                if (i + 1 == sz && sat::hint_type::bound_h == hint.m_ty) {
                    if (!achecker.add_conseq(coeff, e, lit.sign())) {
                        std::cout << "p failed checking hint " << e << "\n";
                        return false;
                    }
                    
                }
                else if (!achecker.add_ineq(coeff, e, lit.sign())) {
                    std::cout << "p failed checking hint " << e << "\n";
                    return false;
                }
            }

            // achecker.display(std::cout << "checking\n");
            bool ok = achecker.check();

            if (!ok) {
                rational lc(1);
                for (auto const& [coeff, lit] : hint.m_literals) 
                    lc = lcm(lc, denominator(coeff));
                bool is_strict = false;
                expr_ref sum(m);
                for (auto const& [coeff, lit] : hint.m_literals) {
                    app_ref e(to_app(m_b2e[lit.var()]), m);
                    VERIFY(pc.check_arith_literal(!lit.sign(), e, coeff*lc, sum, is_strict));
                    std::cout << "sum: " << sum << "\n";
                }
                sort* s = sum->get_sort();
                if (is_strict) 
                    sum = autil.mk_lt(sum, autil.mk_numeral(rational(0), s));
                else 
                    sum = autil.mk_le(sum, autil.mk_numeral(rational(0), s));
                th_rewriter rw(m);
                rw(sum);
                std::cout << "sum: " << sum << "\n";
                
                for (auto const& [a, b]: hint.m_eqs) {
                    expr* x = exprs[a];
                    expr* y = exprs[b];
                    app_ref e(m.mk_eq(x, y), m);
                    std::cout << e << "\n";
                }
                for (auto const& [a, b]: hint.m_diseqs) {
                    expr* x = exprs[a];
                    expr* y = exprs[b];
                    app_ref e(m.mk_not(m.mk_eq(x, y)), m);
                    std::cout << e << "\n";
                }
                for (auto const& [coeff, lit] : hint.m_literals) {
                    app_ref e(to_app(m_b2e[lit.var()]), m);
                    if (lit.sign()) e = m.mk_not(e);
                    std::cout << e << "\n";
                }
                achecker.display(std::cout);
                std::cout << "p hint not verified\n";
                return false;
            }
           
            std::cout << "p hint verified\n";
            return true;
            break;
        }
        default:
            UNREACHABLE();
            break;
        }
        return false;
    }

#endif
