/*++
Copyright (c) 2020 Microsoft Corporation

--*/

#include<iostream>
#include<fstream>
#include "util/memory_manager.h"
#include "util/statistics.h"
#include "sat/dimacs.h"
#include "sat/sat_solver.h"
#include "sat/sat_drat.h"
#include "smt/smt_solver.h"
#include "shell/drat_frontend.h"
#include "parsers/smt2/smt2parser.h"
#include "cmd_context/cmd_context.h"

class smt_checker {
    ast_manager& m;
    expr_ref_vector const& m_b2e;
    expr_ref_vector m_fresh_exprs;
    expr_ref_vector m_core;
    params_ref m_params;
    scoped_ptr<solver> m_solver;

    expr* fresh(expr* e) {
        unsigned i = e->get_id();
        m_fresh_exprs.reserve(i + 1);
        expr* r = m_fresh_exprs.get(i);
        if (!r) {
            r = m.mk_fresh_const("sk", m.get_sort(e));
            m_fresh_exprs[i] = r;
        }
        return r;
    }

    expr_ref define(expr* e, unsigned depth) {
        expr_ref r(fresh(e), m);
        m_core.push_back(m.mk_eq(r, e));
        if (depth == 0)
            return r;
        r = e;
        if (is_app(e)) {
            expr_ref_vector args(m);
            for (expr* arg : *to_app(e)) 
                args.push_back(define(arg, depth - 1));
            r = m.mk_app(to_app(e)->get_decl(), args.size(), args.c_ptr());
        }
        return r;
    }

    void unfold1(sat::literal_vector const& lits) {
        m_core.reset();
        for (sat::literal lit : lits) {
            expr* e = m_b2e[lit.var()];
            expr_ref fml = define(e, 2);
            if (!lit.sign())
                fml = m.mk_not(fml);
            m_core.push_back(fml);
        }
    }
public:
    smt_checker(expr_ref_vector const& b2e): 
        m(b2e.m()), m_b2e(b2e), m_fresh_exprs(m), m_core(m) {
        m_solver = mk_smt_solver(m, m_params, symbol());
    }
    
    void check_shallow(sat::literal_vector const& lits) {
        unfold1(lits);
        m_solver->push();
        for (auto* c : m_core)
            m_solver->assert_expr(c);
        lbool is_sat = m_solver->check_sat();
        m_solver->pop(1);
        if (is_sat == l_true) {
            std::cout << "did not verify: " << lits << "\n" << m_core << "\n";
            for (sat::literal lit : lits) {
                expr_ref e(m_b2e[lit.var()], m);
                if (lit.sign())
                    e = m.mk_not(e);
                std::cout << e << " ";                
            }
            std::cout << "\n";
        }
    }
};

static void verify_smt(char const* drat_file, char const* smt_file) {
    cmd_context ctx;
    ctx.set_ignore_check(true);
    ctx.set_regular_stream(std::cerr);
    ctx.set_solver_factory(mk_smt_strategic_solver_factory());    
    if (smt_file) {
        std::ifstream smt_in(smt_file);
        if (!parse_smt2_commands(ctx, smt_in)) {            
            std::cerr << "could not read file " << smt_file << "\n";
            return;
        }
    }
    
    std::ifstream ins(drat_file);
    dimacs::drat_parser drat(ins, std::cerr);
    std::function<int(char const* read_theory)> read_theory = [&](char const* r) {
        if (strcmp(r, "euf") == 0)
            return ctx.m().get_basic_family_id();
        return ctx.m().mk_family_id(symbol(r));
    };
    drat.set_read_theory(read_theory);
    params_ref p;
    reslimit lim;
    p.set_bool("drat.check_unsat", true);
    sat::solver solver(p, lim);
    sat::drat drat_checker(solver);
    drat_checker.updt_config();

    expr_ref_vector bool_var2expr(ctx.m());
    expr_ref_vector exprs(ctx.m()), args(ctx.m());
    func_decl* f = nullptr;
    ptr_vector<sort> sorts;

    smt_checker checker(bool_var2expr);

    auto check_smt = [&](dimacs::drat_record const& r) {
        auto const& st = r.m_status;
        if (st.is_input())
            ;
        else if (st.is_sat() && st.is_asserted()) {
            std::cout << "Tseitin tautology " << r;
            checker.check_shallow(r.m_lits);
        }
        else if (st.is_sat())
            ;
        else if (st.is_deleted())
            ;
        else {
            std::cout << "check smt " << r;
            checker.check_shallow(r.m_lits);
            // TBD: shallow check may fail because it doesn't include
            // all RUP units, whish are sometimes required.
        }
    };
    
    for (auto const& r : drat) {
        std::cout << r;
        std::cout.flush();
        switch (r.m_tag) {
        case dimacs::drat_record::tag_t::is_clause:
            for (sat::literal lit : r.m_lits)
                while (lit.var() >= solver.num_vars())
                    solver.mk_var(true);
            drat_checker.add(r.m_lits, r.m_status);
            check_smt(r);
            break;
        case dimacs::drat_record::tag_t::is_node:
            args.reset();
            sorts.reset();
            for (auto n : r.m_args) {
                args.push_back(exprs.get(n));
                sorts.push_back(ctx.m().get_sort(args.back()));
            }
            if (r.m_name[0] == '(') {
                std::cout << "parsing sexprs is TBD\n";
                exit(0);
            }
            f = ctx.find_func_decl(symbol(r.m_name.c_str()), 0, nullptr, args.size(), sorts.c_ptr(), nullptr);
            if (!f) {
                std::cout << "could not find function\n";
                exit(0);
            }
            exprs.reserve(r.m_node_id+1);
            exprs.set(r.m_node_id, ctx.m().mk_app(f, args.size(), args.c_ptr()));
            break;
        case dimacs::drat_record::is_bool_def:
            bool_var2expr.reserve(r.m_node_id+1);
            bool_var2expr.set(r.m_node_id, exprs.get(r.m_args[0]));
            break;
        default:
            UNREACHABLE();
            break;
        }
    }
    statistics st;
    drat_checker.collect_statistics(st);
    std::cout << st << "\n";
}


unsigned read_drat(char const* drat_file, char const* problem_file) {
    if (!problem_file) {
        std::cerr << "No smt2 file provided to checker\n";
        return -1;
    }
    verify_smt(drat_file, problem_file);
    return 0;
}


