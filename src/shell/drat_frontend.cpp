/*++
Copyright (c) 2020 Microsoft Corporation

--*/

#include<iostream>
#include<fstream>
#include "util/memory_manager.h"
#include "sat/dimacs.h"
#include "sat/sat_solver.h"
#include "sat/sat_drat.h"
#include "shell/drat_frontend.h"
#include "parsers/smt2/smt2parser.h"
#include "cmd_context/cmd_context.h"

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
            return 0;
        return ctx.m().mk_family_id(symbol(r));
    };
    drat.set_read_theory(read_theory);
    params_ref p;
    reslimit lim;
    p.set_bool("sat.drat.check_unsat",true);
    p.set_bool("drat.check_unsat",true);
    sat::solver solver(p, lim);
    sat::drat drat_checker(solver);
    drat_checker.updt_config();

    expr_ref_vector bool_var2expr(ctx.m());
    expr_ref_vector exprs(ctx.m()), args(ctx.m());
    func_decl* f = nullptr;
    ptr_vector<sort> sorts;
    
    for (auto const& r : drat) {
        std::cout << r;
        std::cout.flush();
        switch (r.m_tag) {
        case dimacs::drat_record::tag_t::is_clause:
            for (sat::literal lit : r.m_lits)
                while (lit.var() >= solver.num_vars())
                    solver.mk_var(true);
            drat_checker.add(r.m_lits, r.m_status);
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
}

static void verify_cnf(char const* drat_file, char const* cnf_file) {

}

unsigned read_drat(char const* drat_file, char const* problem_file) {
#if 0
    if (!problem_file) {
        std::cerr << "No smt2 file provided to checker\n";
        return -1;
    }
#endif
    verify_smt(drat_file, problem_file);
    return 0;
}


