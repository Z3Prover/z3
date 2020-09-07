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
    p.set_bool("drat.check_unsat",true);
    sat::solver solver(p, lim);
    sat::drat drat_checker(solver);

    expr_ref_vector bool_var2expr(ctx.m());
    expr_ref_vector exprs(ctx.m());
    
    
    for (auto const& r : drat) {
        std::cout << r;
        switch (r.m_tag) {
        case dimacs::drat_record::tag_t::is_clause:
            // TODO check propositional and SMT consequences here
            // drat_checker.add(r.m_lits, r.m_status);
            break;
        case dimacs::drat_record::tag_t::is_node:
            // TODO: create AST nodes
            break;
        case dimacs::drat_record::is_bool_def:
            // TODO: map bool-vars to AST nodes.
            // bool_var2expr.set(r.m_node_id, exprs.get(r.m_args[0]));
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


