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

class smt_checker {
    ast_manager& m;
    sat::drat& m_drat;
    expr_ref_vector const& m_b2e;
    expr_ref_vector m_fresh_exprs;
    expr_ref_vector m_core;
    expr_ref_vector m_inputs;
    params_ref m_params;
    scoped_ptr<solver> m_lemma_solver, m_input_solver;
    sat::literal_vector m_units;
    bool m_check_inputs { false };

    expr* fresh(expr* e) {
        unsigned i = e->get_id();
        m_fresh_exprs.reserve(i + 1);
        expr* r = m_fresh_exprs.get(i);
        if (!r) {
            r = m.mk_fresh_const("sk", e->get_sort());
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
            r = m.mk_app(to_app(e)->get_decl(), args.size(), args.data());
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

    expr_ref lit2expr(sat::literal lit) {
        return expr_ref(lit.sign() ? m.mk_not(m_b2e[lit.var()]) : m_b2e[lit.var()], m);
    }

    void add_units() {
        auto const& units = m_drat.units();
#if 0
        for (unsigned i = m_units.size(); i < units.size(); ++i) {
            sat::literal lit = units[i];            
            m_lemma_solver->assert_expr(lit2expr(lit));
        }
#endif
        m_units.append(units.size() - m_units.size(), units.data() + m_units.size());
    }

    void check_assertion_redundant(sat::literal_vector const& input) {
        expr_ref_vector args(m);
        for (auto lit : input)
            args.push_back(lit2expr(lit));
        m_inputs.push_back(args.size() == 1 ? args.back() : m.mk_or(args));

        m_input_solver->push();
        for (auto lit : input) {
            m_input_solver->assert_expr(lit2expr(~lit));
        }
        lbool is_sat = m_input_solver->check_sat();
        if (is_sat != l_false) {
            std::cout << "Failed to verify input\n";
            exit(0);
        }
        m_input_solver->pop(1);
    }


    /**
    * Validate a lemma using the following attempts:
    * 1. check if it is propositional DRUP
    * 2. establish the negation of literals is unsat using a limited unfolding.
    * 3. check that it is DRUP modulo theories by taking propositional implicants from DRUP validation
    */
    sat::literal_vector drup_units;

    void check_clause(sat::literal_vector const& lits) {
        
        add_units();
        drup_units.reset();
        if (m_drat.is_drup(lits.size(), lits.data(), drup_units)) {
            std::cout << "drup\n";
            return;
        }
        m_input_solver->push();
//        for (auto lit : drup_units)
//            m_input_solver->assert_expr(lit2expr(lit));
        for (auto lit : lits)
            m_input_solver->assert_expr(lit2expr(~lit));
        lbool is_sat = m_input_solver->check_sat();
        if (is_sat != l_false) {
            std::cout << "did not verify: " << lits << "\n";
            for (sat::literal lit : lits) {
                std::cout << lit2expr(lit) << "\n";
            }
            std::cout << "\n";
            m_input_solver->display(std::cout);
            exit(0);
        }
        m_input_solver->pop(1);
        std::cout << "smt\n";
        // check_assertion_redundant(lits);
    }

public:
    smt_checker(sat::drat& drat, expr_ref_vector const& b2e): 
        m(b2e.m()), m_drat(drat), m_b2e(b2e), m_fresh_exprs(m), m_core(m), m_inputs(m) {
        m_lemma_solver = mk_smt_solver(m, m_params, symbol());
        m_input_solver = mk_smt_solver(m, m_params, symbol());
    }

    void add(sat::literal_vector const& lits, sat::status const& st) {
        for (sat::literal lit : lits)
            while (lit.var() >= m_drat.get_solver().num_vars())
                m_drat.get_solver().mk_var(true);
        if (st.is_input() && m_check_inputs)
            check_assertion_redundant(lits);
        else if (!st.is_sat() && !st.is_deleted()) 
            check_clause(lits);        
        // m_drat.add(lits, st);
    }    

    /**
    * Add an assertion from the source file
    */
    void add_assertion(expr* a) {
        m_input_solver->assert_expr(a);
    }

    void display_input() {
        scoped_ptr<solver> s = mk_smt_solver(m, m_params, symbol());
        for (auto* e : m_inputs)
            s->assert_expr(e);
        s->display(std::cout);
    }

    symbol name;
    unsigned_vector params;
    ptr_vector<sort> sorts;

    void parse_sexpr(sexpr_ref const& sexpr, cmd_context& ctx, expr_ref_vector const& args, expr_ref& result) {
        params.reset();
        sorts.reset();
        for (expr* arg : args) 
            sorts.push_back(arg->get_sort());
        sort_ref rng(m);
        func_decl* f = nullptr;
        switch (sexpr->get_kind()) {
        case sexpr::kind_t::COMPOSITE: {
            unsigned sz = sexpr->get_num_children();
            if (sz == 0) 
                goto bail;
            if (sexpr->get_child(0)->get_symbol() == symbol("_")) {
                name = sexpr->get_child(1)->get_symbol();
                if (name == "bv" && sz == 4) {
                    bv_util bvu(m);
                    auto val = sexpr->get_child(2)->get_numeral();
                    auto n   = sexpr->get_child(3)->get_numeral().get_unsigned();
                    result = bvu.mk_numeral(val, n);
                    return;
                }
                if (name == "is" && sz == 3) {
                    name = sexpr->get_child(2)->get_child(0)->get_symbol();
                    f = ctx.find_func_decl(name, params.size(), params.data(), args.size(), sorts.data(), rng.get());
                    if (!f)
                        goto bail;
                    datatype_util dtu(m);
                    result = dtu.mk_is(f, args[0]);
                    return;
                }
                if (name == "Real" && sz == 4) {
                    arith_util au(m);
                    rational r = sexpr->get_child(2)->get_numeral();
                    // rational den = sexpr->get_child(3)->get_numeral();
                    result = au.mk_numeral(r, false);
                    return;
                }
                if (name == "Int" && sz == 4) {
                    arith_util au(m);
                    rational num = sexpr->get_child(2)->get_numeral();
                    result = au.mk_numeral(num, true);
                    return;
                }
                for (unsigned i = 2; i < sz; ++i) {
                    auto* child = sexpr->get_child(i);
                    if (child->is_numeral() && child->get_numeral().is_unsigned())
                        params.push_back(child->get_numeral().get_unsigned());
                    else 
                        goto bail;                
                }
                break;
            }
            goto bail;
        }
        case sexpr::kind_t::SYMBOL:
            name = sexpr->get_symbol();
            break;
        case sexpr::kind_t::BV_NUMERAL: {
            std::cout << "bv numeral\n";
            goto bail;            
        }
        case sexpr::kind_t::STRING:
        case sexpr::kind_t::KEYWORD:
        case sexpr::kind_t::NUMERAL:
        default:
            goto bail;
        }
        f = ctx.find_func_decl(name, params.size(), params.data(), args.size(), sorts.data(), rng.get());
        if (!f) 
            goto bail;
        result = ctx.m().mk_app(f, args);
        return;
    bail:
        std::cout << "Could not parse expression\n";
        sexpr->display(std::cout);
        std::cout << "\n";
        exit(0);        
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
    ast_manager& m = ctx.m();
    std::function<int(char const* read_theory)> read_theory = [&](char const* r) {
        return m.mk_family_id(symbol(r));
    };
    std::function<symbol(int)> write_theory = [&](int th) {
        return m.get_family_name(th);
    };
    drat.set_read_theory(read_theory);
    params_ref p;
    reslimit lim;
    p.set_bool("drat.check_unsat", true);
    sat::solver solver(p, lim);
    sat::drat drat_checker(solver);
    drat_checker.updt_config();

    expr_ref_vector bool_var2expr(m);
    expr_ref_vector exprs(m), args(m), inputs(m);
    sort_ref_vector sargs(m), sorts(m);
    func_decl_ref_vector decls(m);

    smt_checker checker(drat_checker, bool_var2expr);

    for (expr* a : ctx.assertions())
        checker.add_assertion(a);

    for (auto const& r : drat) {
        std::cout << dimacs::drat_pp(r, write_theory); 
        std::cout.flush();
        switch (r.m_tag) {
        case dimacs::drat_record::tag_t::is_clause:
            checker.add(r.m_lits, r.m_status);
            if (drat_checker.inconsistent()) {
                std::cout << "inconsistent\n";
                return;
            }            
            break;
        case dimacs::drat_record::tag_t::is_node: {
            expr_ref e(m);
            args.reset();
            for (auto n : r.m_args) 
                args.push_back(exprs.get(n));
            std::istringstream strm(r.m_name);
            auto sexpr = parse_sexpr(ctx, strm, p, drat_file);
            checker.parse_sexpr(sexpr, ctx, args, e);
            exprs.reserve(r.m_node_id+1);
            exprs.set(r.m_node_id, e);
            break;
        }
        case dimacs::drat_record::tag_t::is_decl: {
            std::istringstream strm(r.m_name);
            ctx.set_allow_duplicate_declarations();
            parse_smt2_commands(ctx, strm);
            break;
        }
        case dimacs::drat_record::tag_t::is_sort: {
            sort_ref srt(m);
            symbol name = symbol(r.m_name.c_str());
            sargs.reset();
            for (auto n : r.m_args) 
                sargs.push_back(sorts.get(n));
            psort_decl* pd = ctx.find_psort_decl(name);
            if (pd) 
                srt = pd->instantiate(ctx.pm(), sargs.size(), sargs.data());
            else 
                srt = m.mk_uninterpreted_sort(name);
            sorts.reserve(r.m_node_id+1);
            sorts.set(r.m_node_id, srt);
            break;
        }
        case dimacs::drat_record::tag_t::is_bool_def:
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


