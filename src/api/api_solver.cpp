/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    api_solver.cpp

Abstract:

    Solver API

Author:

    Leonardo de Moura (leonardo) 2012-03-07.

Revision History:

--*/
#include<thread>
#include "util/scoped_ctrl_c.h"
#include "util/cancel_eh.h"
#include "util/file_path.h"
#include "util/scoped_timer.h"
#include "util/file_path.h"
#include "ast/ast_pp.h"
#include "api/z3.h"
#include "api/api_log_macros.h"
#include "api/api_context.h"
#include "api/api_tactic.h"
#include "api/api_solver.h"
#include "api/api_model.h"
#include "api/api_stats.h"
#include "api/api_ast_vector.h"
#include "model/model_params.hpp"
#include "smt/smt_solver.h"
#include "smt/smt_implied_equalities.h"
#include "solver/smt_logics.h"
#include "solver/tactic2solver.h"
#include "params/solver_params.hpp"
#include "cmd_context/cmd_context.h"
#include "parsers/smt2/smt2parser.h"
#include "sat/dimacs.h"
#include "sat/sat_solver.h"
#include "sat/tactic/goal2sat.h"
#include "sat/tactic/sat2goal.h"
#include "cmd_context/extra_cmds/proof_cmds.h"
#include "solver/simplifier_solver.h"


extern "C" {

    void solver2smt2_pp::assert_expr(expr* e) {
        m_pp_util.collect(e);
        m_pp_util.display_decls(m_out);
        m_pp_util.display_assert(m_out, e, true);
    }

    void solver2smt2_pp::assert_expr(expr* e, expr* t) {
        m_pp_util.collect(e);
        m_pp_util.collect(t);
        m_pp_util.display_decls(m_out);
        m_pp_util.display_assert_and_track(m_out, e, t, true);
        m_tracked.push_back(t);
    }

    void solver2smt2_pp::push() {
        m_out << "(push 1)\n";
        m_pp_util.push();
        m_tracked_lim.push_back(m_tracked.size());
    }

    void solver2smt2_pp::pop(unsigned n) {
        m_out << "(pop " << n << ")\n";
        m_pp_util.pop(n);
        m_tracked.shrink(m_tracked_lim[m_tracked_lim.size() - n]);
        m_tracked_lim.shrink(m_tracked_lim.size() - n);
    }

    void solver2smt2_pp::reset() {
        m_out << "(reset)\n";
        m_pp_util.reset();        
    }

    void solver2smt2_pp::check(unsigned n, expr* const* asms) {
        for (unsigned i = 0; i < n; ++i) 
            m_pp_util.collect(asms[i]);
        m_pp_util.display_decls(m_out);
        m_out << "(check-sat";        
        for (unsigned i = 0; i < n; ++i) 
            m_pp_util.display_expr(m_out << "\n", asms[i]);            
        for (expr* e : m_tracked) 
            m_pp_util.display_expr(m_out << "\n", e);
        m_out << ")\n";
        m_out.flush();
    }

    void solver2smt2_pp::get_consequences(expr_ref_vector const& assumptions, expr_ref_vector const& variables) {
        for (expr* a : assumptions)
            m_pp_util.collect(a);
        for (expr* v : variables)
            m_pp_util.collect(v);
        m_pp_util.display_decls(m_out);        
        m_out << "(get-consequences (";
        for (expr* f : assumptions) {
            m_out << "\n";
            m_pp_util.display_expr(m_out, f);
        }
        m_out << ") (";
        for (expr* f : variables) {
            m_out << "\n";
            m_pp_util.display_expr(m_out, f);
        }
        m_out << "))\n";
        m_out.flush();
    }

    solver2smt2_pp::solver2smt2_pp(ast_manager& m, const std::string& file):
        m_pp_util(m), m_out(file, std::ofstream::trunc | std::ofstream::out), m_tracked(m) {
        if (!m_out) {
            throw default_exception("could not open " + file + " for output");
        }
    }

    void Z3_solver_ref::set_eh(event_handler* eh) {
        lock_guard lock(m_mux);
        m_eh = eh;
    }

    void Z3_solver_ref::set_cancel() {
        lock_guard lock(m_mux);
        if (m_eh) (*m_eh)(API_INTERRUPT_EH_CALLER);
    }

    void Z3_solver_ref::assert_expr(expr * e) {
        if (m_pp) m_pp->assert_expr(e);
        m_solver->assert_expr(e);
    }

    void Z3_solver_ref::assert_expr(expr * e, expr* t) {
        if (m_pp) m_pp->assert_expr(e, t);
        m_solver->assert_expr(e, t);
    }

    static void init_solver_core(Z3_context c, Z3_solver _s) {
        Z3_solver_ref * s = to_solver(_s);
        bool proofs_enabled = true, models_enabled = true, unsat_core_enabled = false;
        params_ref p = s->m_params;
        mk_c(c)->params().get_solver_params(p, proofs_enabled, models_enabled, unsat_core_enabled);
        s->m_solver = (*(s->m_solver_factory))(mk_c(c)->m(), p, proofs_enabled, models_enabled, unsat_core_enabled, s->m_logic);
        
        param_descrs r;
        s->m_solver->collect_param_descrs(r);
        context_params::collect_solver_param_descrs(r);
        p.validate(r);
        s->m_solver->updt_params(p);
    }

    static void init_solver(Z3_context c, Z3_solver s) {
        if (to_solver(s)->m_solver.get() == nullptr)
            init_solver_core(c, s);
    }


    static void init_solver_log(Z3_context c, Z3_solver s) {
        static std::thread::id g_thread_id = std::this_thread::get_id();
        static bool g_is_threaded = false;
        solver_params sp(to_solver(s)->m_params);
        symbol smt2log = sp.smtlib2_log();
        if (smt2log.is_non_empty_string() && !to_solver(s)->m_pp) {
            if (g_is_threaded || g_thread_id != std::this_thread::get_id()) {
                g_is_threaded = true;
                std::ostringstream strm;
                strm << smt2log << '-' << std::this_thread::get_id();
                smt2log = symbol(std::move(strm).str());
            }
            to_solver(s)->m_pp = alloc(solver2smt2_pp, mk_c(c)->m(), smt2log.str());
        }
    }

    Z3_solver Z3_API Z3_mk_simple_solver(Z3_context c) {
        Z3_TRY;
        LOG_Z3_mk_simple_solver(c);
        RESET_ERROR_CODE();
        Z3_solver_ref * s = alloc(Z3_solver_ref, *mk_c(c), mk_smt_solver_factory());
        mk_c(c)->save_object(s);
        Z3_solver r = of_solver(s);
        init_solver_log(c, r);
        RETURN_Z3(r);
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_solver Z3_API Z3_mk_solver(Z3_context c) {
        Z3_TRY;
        LOG_Z3_mk_solver(c);
        RESET_ERROR_CODE();
        Z3_solver_ref * s = alloc(Z3_solver_ref, *mk_c(c), mk_smt_strategic_solver_factory());
        mk_c(c)->save_object(s);
        Z3_solver r = of_solver(s);
        init_solver_log(c, r);
        RETURN_Z3(r);
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_solver Z3_API Z3_mk_solver_for_logic(Z3_context c, Z3_symbol logic) {
        Z3_TRY;
        LOG_Z3_mk_solver_for_logic(c, logic);
        RESET_ERROR_CODE();
        if (!smt_logics::supported_logic(to_symbol(logic))) {
            std::ostringstream strm;
            strm << "logic '" << to_symbol(logic) << "' is not recognized";
            SET_ERROR_CODE(Z3_INVALID_ARG, std::move(strm).str());
            RETURN_Z3(nullptr);
        }
        else {
            Z3_solver_ref * s = alloc(Z3_solver_ref, *mk_c(c), mk_smt_strategic_solver_factory(to_symbol(logic)));
            mk_c(c)->save_object(s);
            Z3_solver r = of_solver(s);
            init_solver_log(c, r);
            RETURN_Z3(r);
        }
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_solver Z3_API Z3_mk_solver_from_tactic(Z3_context c, Z3_tactic t) {
        Z3_TRY;
        LOG_Z3_mk_solver_from_tactic(c, t);
        RESET_ERROR_CODE();
        Z3_solver_ref * s = alloc(Z3_solver_ref, *mk_c(c), mk_tactic2solver_factory(to_tactic_ref(t)));
        mk_c(c)->save_object(s);
        Z3_solver r = of_solver(s);
        init_solver_log(c, r);
        RETURN_Z3(r);
        Z3_CATCH_RETURN(nullptr);
    }

    /**
    * attach a simplifier to solver.
    * This is legal when the solver is fresh, does not already have assertions (and scopes).
    * To allow recycling the argument solver, we create a fresh copy of it and pass it to 
    * mk_simplifier_solver.
    */
    Z3_solver Z3_API Z3_solver_add_simplifier(Z3_context c, Z3_solver solver, Z3_simplifier simplifier) {
        Z3_TRY;
        LOG_Z3_solver_add_simplifier(c, solver, simplifier); 
        solver_ref s_fresh;
        if (to_solver(solver)->m_solver) {
            s_fresh = to_solver_ref(solver)->translate(mk_c(c)->m(), to_solver(solver)->m_params);
        }
        else {
            // create the solver, but hijack it for internal uses.
            init_solver(c, solver);
            s_fresh = to_solver(solver)->m_solver;
            to_solver(solver)->m_solver = nullptr;
        }
        if (!s_fresh) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "unexpected empty solver state");
            RETURN_Z3(nullptr);
        }
        if (s_fresh->get_num_assertions() > 0) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "adding a simplifier to a solver with assertions is not allowed.");
            RETURN_Z3(nullptr);
        }        
        auto simp = to_simplifier_ref(simplifier);
        auto* simplifier_solver = mk_simplifier_solver(s_fresh.get(), simp);
        Z3_solver_ref* result = alloc(Z3_solver_ref, *mk_c(c), simplifier_solver);
        mk_c(c)->save_object(result);
        RETURN_Z3(of_solver(result));
        Z3_CATCH_RETURN(nullptr);
    }


    Z3_solver Z3_API Z3_solver_translate(Z3_context c, Z3_solver s, Z3_context target) {
        Z3_TRY;
        LOG_Z3_solver_translate(c, s, target);
        RESET_ERROR_CODE();
        params_ref const& p = to_solver(s)->m_params; 
        Z3_solver_ref * sr = alloc(Z3_solver_ref, *mk_c(target), (solver_factory *)nullptr);
        init_solver(c, s);
        sr->m_solver = to_solver(s)->m_solver->translate(mk_c(target)->m(), p);
        mk_c(target)->save_object(sr);
        Z3_solver r = of_solver(sr);
        init_solver_log(target, r);
        RETURN_Z3(r);
        Z3_CATCH_RETURN(nullptr);
    }


    void Z3_API Z3_solver_import_model_converter(Z3_context c, Z3_solver src, Z3_solver dst) {
        Z3_TRY;
        LOG_Z3_solver_import_model_converter(c, src, dst);
        model_converter_ref mc = to_solver_ref(src)->get_model_converter();
        to_solver_ref(dst)->set_model_converter(mc.get());
        Z3_CATCH;
    }

    void solver_from_stream(Z3_context c, Z3_solver s, std::istream& is) {
        auto& solver = *to_solver(s);
        if (!solver.m_cmd_context) {
            solver.m_cmd_context = alloc(cmd_context, false, &(mk_c(c)->m()));
            install_proof_cmds(*solver.m_cmd_context);            
        }
        auto& ctx = solver.m_cmd_context;
        ctx->set_ignore_check(true);
        std::stringstream errstrm;
        ctx->set_regular_stream(errstrm);

        if (!parse_smt2_commands(*ctx.get(), is)) {
            ctx = nullptr;
            SET_ERROR_CODE(Z3_PARSER_ERROR, std::move(errstrm).str());
            return;
        }


        bool initialized = to_solver(s)->m_solver.get() != nullptr;
        if (!initialized)
            init_solver(c, s);
        for (auto const& [asr, an] : ctx->tracked_assertions())
            if (an)
                to_solver(s)->assert_expr(asr, an);
            else
                to_solver(s)->assert_expr(asr);
        ctx->reset_tracked_assertions();
        to_solver_ref(s)->set_model_converter(ctx->get_model_converter());
        auto* ctx_s = ctx->get_solver();
        if (ctx_s && ctx_s->get_proof())
            to_solver_ref(s)->set_proof(ctx_s->get_proof());

    }

    static void solver_from_dimacs_stream(Z3_context c, Z3_solver s, std::istream& is) {
        init_solver(c, s);
        ast_manager& m = to_solver_ref(s)->get_manager();
        std::stringstream err;
        sat::solver solver(to_solver_ref(s)->get_params(), m.limit());
        if (!parse_dimacs(is, err, solver)) {
            SET_ERROR_CODE(Z3_PARSER_ERROR, std::move(err).str());
            return;
        }
        sat2goal s2g;
        ref<sat2goal::mc> mc;
        atom2bool_var a2b(m);
        for (unsigned v = 0; v < solver.num_vars(); ++v) {
            a2b.insert(m.mk_const(symbol(v), m.mk_bool_sort()), v);
        }
        goal g(m);            
        s2g(solver, a2b, to_solver_ref(s)->get_params(), g, mc);
        for (unsigned i = 0; i < g.size(); ++i) {
            to_solver(s)->assert_expr(g.form(i));
        }
    }

    // DIMACS files start with "p cnf" and number of variables/clauses.
    // This is not legal SMT syntax, so use the DIMACS parser.
    static bool is_dimacs_string(Z3_string c_str) {
        return c_str[0] == 'p' && c_str[1] == ' ' && c_str[2] == 'c';
    }

    void Z3_API Z3_solver_from_string(Z3_context c, Z3_solver s, Z3_string c_str) {
        Z3_TRY;
        LOG_Z3_solver_from_string(c, s, c_str);
        std::istringstream is(c_str);
        if (is_dimacs_string(c_str)) {
            solver_from_dimacs_stream(c, s, is);
        }
        else {
            solver_from_stream(c, s, is);
        }
        Z3_CATCH;        
    }

    void Z3_API Z3_solver_from_file(Z3_context c, Z3_solver s, Z3_string file_name) {
        Z3_TRY;
        LOG_Z3_solver_from_file(c, s, file_name);
        char const* ext = get_extension(file_name);
        std::ifstream is(file_name);
        init_solver(c, s);
        if (!is) {
            SET_ERROR_CODE(Z3_FILE_ACCESS_ERROR, nullptr);
        }
        else if (ext && (std::string("dimacs") == ext || std::string("cnf") == ext)) {
            solver_from_dimacs_stream(c, s, is);
        }
        else {
            solver_from_stream(c, s, is);
        }
        Z3_CATCH;
    }

    Z3_string Z3_API Z3_solver_get_help(Z3_context c, Z3_solver s) {
        Z3_TRY;
        LOG_Z3_solver_get_help(c, s);
        RESET_ERROR_CODE();
        std::ostringstream buffer;
        param_descrs descrs;
        bool initialized = to_solver(s)->m_solver.get() != nullptr;
        if (!initialized)
            init_solver(c, s);
        to_solver_ref(s)->collect_param_descrs(descrs);
        context_params::collect_solver_param_descrs(descrs);
        if (!initialized)
            to_solver(s)->m_solver = nullptr;
        descrs.display(buffer);
        return mk_c(c)->mk_external_string(std::move(buffer).str());
        Z3_CATCH_RETURN("");
    }

    Z3_param_descrs Z3_API Z3_solver_get_param_descrs(Z3_context c, Z3_solver s) {
        Z3_TRY;
        LOG_Z3_solver_get_param_descrs(c, s);
        RESET_ERROR_CODE();
        Z3_param_descrs_ref * d = alloc(Z3_param_descrs_ref, *mk_c(c));
        mk_c(c)->save_object(d);
        bool initialized = to_solver(s)->m_solver.get() != nullptr;
        if (!initialized)
            init_solver(c, s);
        to_solver_ref(s)->collect_param_descrs(d->m_descrs);
        context_params::collect_solver_param_descrs(d->m_descrs);
        if (!initialized)
            to_solver(s)->m_solver = nullptr;
        Z3_param_descrs r = of_param_descrs(d);
        RETURN_Z3(r);
        Z3_CATCH_RETURN(nullptr);
    }


    void Z3_API Z3_solver_set_params(Z3_context c, Z3_solver s, Z3_params p) {
        Z3_TRY;
        LOG_Z3_solver_set_params(c, s, p);
        RESET_ERROR_CODE();

        auto &params = to_param_ref(p);
        symbol logic = params.get_sym("smt.logic", symbol::null);
        if (logic != symbol::null) {
            to_solver(s)->m_logic = logic;
        }
        if (to_solver(s)->m_solver) {
            bool old_model = to_solver(s)->m_params.get_bool("model", true);
            bool new_model = params.get_bool("model", true);
            if (old_model != new_model)
                to_solver_ref(s)->set_produce_models(new_model);
            param_descrs& r = to_solver(s)->m_param_descrs;
            if(r.size () == 0) {
              to_solver_ref(s)->collect_param_descrs(r);
              context_params::collect_solver_param_descrs(r);
            }
            params.validate(r);
            to_solver_ref(s)->updt_params(params);
        }
        auto& solver = *to_solver(s);        
        solver.m_params.append(params);
        
        if (solver.m_cmd_context && solver.m_cmd_context->get_proof_cmds())
            solver.m_cmd_context->get_proof_cmds()->updt_params(solver.m_params);

        init_solver_log(c, s);
        
        Z3_CATCH;
    }
    
    void Z3_API Z3_solver_inc_ref(Z3_context c, Z3_solver s) {
        Z3_TRY;
        LOG_Z3_solver_inc_ref(c, s);
        RESET_ERROR_CODE();
        to_solver(s)->inc_ref();
        Z3_CATCH;
    }

    void Z3_API Z3_solver_dec_ref(Z3_context c, Z3_solver s) {
        Z3_TRY;
        LOG_Z3_solver_dec_ref(c, s);
        if (s) 
            to_solver(s)->dec_ref();        
        Z3_CATCH;
    }

    void Z3_API Z3_solver_push(Z3_context c, Z3_solver s) {
        Z3_TRY;
        LOG_Z3_solver_push(c, s);
        RESET_ERROR_CODE();
        init_solver(c, s);
        to_solver_ref(s)->push();
        if (to_solver(s)->m_pp) to_solver(s)->m_pp->push();
        Z3_CATCH;
    }

    void Z3_API Z3_solver_interrupt(Z3_context c, Z3_solver s) {
        to_solver(s)->set_cancel();
    }

    void Z3_API Z3_solver_pop(Z3_context c, Z3_solver s, unsigned n) {
        Z3_TRY;
        LOG_Z3_solver_pop(c, s, n);
        RESET_ERROR_CODE();
        init_solver(c, s);
        if (n > to_solver_ref(s)->get_scope_level()) {
            SET_ERROR_CODE(Z3_IOB, nullptr);
            return;
        }
        if (n > 0) {
            to_solver_ref(s)->pop(n);
            if (to_solver(s)->m_pp) to_solver(s)->m_pp->pop(n);
        }
        Z3_CATCH;
    }

    void Z3_API Z3_solver_reset(Z3_context c, Z3_solver s) {
        Z3_TRY;
        LOG_Z3_solver_reset(c, s);
        RESET_ERROR_CODE();
        to_solver(s)->m_solver = nullptr;
        to_solver(s)->m_cmd_context = nullptr;
        if (to_solver(s)->m_pp) to_solver(s)->m_pp->reset();
        Z3_CATCH;
    }
    
    unsigned Z3_API Z3_solver_get_num_scopes(Z3_context c, Z3_solver s) {
        Z3_TRY;
        LOG_Z3_solver_get_num_scopes(c, s);
        RESET_ERROR_CODE();
        init_solver(c, s);
        return to_solver_ref(s)->get_scope_level();
        Z3_CATCH_RETURN(0);
    }
    
    void Z3_API Z3_solver_assert(Z3_context c, Z3_solver s, Z3_ast a) {
        Z3_TRY;
        LOG_Z3_solver_assert(c, s, a);
        RESET_ERROR_CODE();
        init_solver(c, s);
        CHECK_FORMULA(a,);
        to_solver(s)->assert_expr(to_expr(a));
        Z3_CATCH;
    }

    void Z3_API Z3_solver_assert_and_track(Z3_context c, Z3_solver s, Z3_ast a, Z3_ast p) {
        Z3_TRY;
        LOG_Z3_solver_assert_and_track(c, s, a, p);
        RESET_ERROR_CODE();
        init_solver(c, s);
        CHECK_FORMULA(a,);
        CHECK_FORMULA(p,);
        to_solver(s)->assert_expr(to_expr(a), to_expr(p));
        Z3_CATCH;
    }

    
    Z3_ast_vector Z3_API Z3_solver_get_assertions(Z3_context c, Z3_solver s) {
        Z3_TRY;
        LOG_Z3_solver_get_assertions(c, s);
        RESET_ERROR_CODE();
        init_solver(c, s);
        Z3_ast_vector_ref * v = alloc(Z3_ast_vector_ref, *mk_c(c), mk_c(c)->m());
        mk_c(c)->save_object(v);
        unsigned sz = to_solver_ref(s)->get_num_assertions();
        for (unsigned i = 0; i < sz; i++) {
            v->m_ast_vector.push_back(to_solver_ref(s)->get_assertion(i));
        }
        RETURN_Z3(of_ast_vector(v));
        Z3_CATCH_RETURN(nullptr);
    }


    Z3_ast_vector Z3_API Z3_solver_get_units(Z3_context c, Z3_solver s) {
        Z3_TRY;
        LOG_Z3_solver_get_units(c, s);
        RESET_ERROR_CODE();
        init_solver(c, s);
        Z3_ast_vector_ref * v = alloc(Z3_ast_vector_ref, *mk_c(c), mk_c(c)->m());
        mk_c(c)->save_object(v);
        expr_ref_vector fmls = to_solver_ref(s)->get_units();
        for (expr* f : fmls) {
            v->m_ast_vector.push_back(f);
        }
        RETURN_Z3(of_ast_vector(v));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast_vector Z3_API Z3_solver_get_non_units(Z3_context c, Z3_solver s) {
        Z3_TRY;
        LOG_Z3_solver_get_non_units(c, s);
        RESET_ERROR_CODE();
        init_solver(c, s);
        Z3_ast_vector_ref * v = alloc(Z3_ast_vector_ref, *mk_c(c), mk_c(c)->m());
        mk_c(c)->save_object(v);
        expr_ref_vector fmls = to_solver_ref(s)->get_non_units();
        for (expr* f : fmls) {
            v->m_ast_vector.push_back(f);
        }
        RETURN_Z3(of_ast_vector(v));
        Z3_CATCH_RETURN(nullptr);
    }

    void Z3_API Z3_solver_get_levels(Z3_context c, Z3_solver s, Z3_ast_vector literals, unsigned sz, unsigned levels[]) {
        Z3_TRY;
        LOG_Z3_solver_get_levels(c, s, literals, sz, levels);
        RESET_ERROR_CODE();
        init_solver(c, s);
        if (sz != Z3_ast_vector_size(c, literals)) {
            SET_ERROR_CODE(Z3_IOB, nullptr);
            return;
        }
        ptr_vector<expr> _vars;
        for (unsigned i = 0; i < sz; ++i) {
            expr* e = to_expr(Z3_ast_vector_get(c, literals, i));
            mk_c(c)->m().is_not(e, e);
            _vars.push_back(e);
        }
        unsigned_vector _levels(sz);
        to_solver_ref(s)->get_levels(_vars, _levels);
        for (unsigned i = 0; i < sz; ++i) {
            levels[i] = _levels[i];
        }
        Z3_CATCH;
    }

    Z3_ast_vector Z3_API Z3_solver_get_trail(Z3_context c, Z3_solver s) {
        Z3_TRY;
        LOG_Z3_solver_get_trail(c, s);
        RESET_ERROR_CODE();
        init_solver(c, s);
        Z3_ast_vector_ref * v = alloc(Z3_ast_vector_ref, *mk_c(c), mk_c(c)->m());
        mk_c(c)->save_object(v);
        expr_ref_vector trail = to_solver_ref(s)->get_trail(UINT_MAX);
        for (expr* f : trail) {
            v->m_ast_vector.push_back(f);
        }
        RETURN_Z3(of_ast_vector(v));
        Z3_CATCH_RETURN(nullptr);
    }

#define STRINGIFY(x) #x
#define TOSTRING(x) STRINGIFY(x)    

    static Z3_lbool _solver_check(Z3_context c, Z3_solver s, unsigned num_assumptions, Z3_ast const assumptions[]) {
        for (unsigned i = 0; i < num_assumptions; i++) {
            if (!is_expr(to_ast(assumptions[i]))) {
                SET_ERROR_CODE(Z3_INVALID_ARG, "assumption is not an expression");
                return Z3_L_UNDEF;
            }
        }
        expr * const * _assumptions = to_exprs(num_assumptions, assumptions);
        solver_params sp(to_solver(s)->m_params);
        unsigned timeout     = mk_c(c)->get_timeout();
        timeout              = to_solver(s)->m_params.get_uint("timeout", timeout);
        timeout              = sp.timeout() != UINT_MAX ? sp.timeout() : timeout;
        unsigned rlimit      = to_solver(s)->m_params.get_uint("rlimit", mk_c(c)->get_rlimit());
        bool     use_ctrl_c  = to_solver(s)->m_params.get_bool("ctrl_c", true);
        cancel_eh<reslimit> eh(mk_c(c)->m().limit());
        to_solver(s)->set_eh(&eh);
        api::context::set_interruptable si(*(mk_c(c)), eh);
        lbool result = l_undef;
        {
            scoped_ctrl_c ctrlc(eh, false, use_ctrl_c);
            scoped_timer timer(timeout, &eh);
            scoped_rlimit _rlimit(mk_c(c)->m().limit(), rlimit);
            try {
                if (to_solver(s)->m_pp) to_solver(s)->m_pp->check(num_assumptions, _assumptions); 
                result = to_solver_ref(s)->check_sat(num_assumptions, _assumptions);
            }
            catch (z3_exception & ex) {
                to_solver_ref(s)->set_reason_unknown(eh, ex);
                to_solver(s)->set_eh(nullptr);
                if (mk_c(c)->m().inc()) {
                    mk_c(c)->handle_exception(ex);
                }
                return Z3_L_UNDEF;
            }
            catch (std::exception& ex) {
                to_solver_ref(s)->set_reason_unknown(eh, ex);
                to_solver(s)->set_eh(nullptr);
                return Z3_L_UNDEF;
            }
        }
        to_solver(s)->set_eh(nullptr);
        if (result == l_undef) {
            to_solver_ref(s)->set_reason_unknown(eh, __FILE__ ":" TOSTRING(__LINE__));
        }
        return static_cast<Z3_lbool>(result);
    }
    
    Z3_lbool Z3_API Z3_solver_check(Z3_context c, Z3_solver s) {
        Z3_TRY;
        LOG_Z3_solver_check(c, s);
        RESET_ERROR_CODE();
        init_solver(c, s);
        return _solver_check(c, s, 0, nullptr);
        Z3_CATCH_RETURN(Z3_L_UNDEF);
    }

    Z3_lbool Z3_API Z3_solver_check_assumptions(Z3_context c, Z3_solver s, unsigned num_assumptions, Z3_ast const assumptions[]) {
        Z3_TRY;
        LOG_Z3_solver_check_assumptions(c, s, num_assumptions, assumptions);
        RESET_ERROR_CODE();
        init_solver(c, s);
        return _solver_check(c, s, num_assumptions, assumptions);
        Z3_CATCH_RETURN(Z3_L_UNDEF);
    }
    
    Z3_model Z3_API Z3_solver_get_model(Z3_context c, Z3_solver s) {
        Z3_TRY;
        LOG_Z3_solver_get_model(c, s);
        RESET_ERROR_CODE();
        init_solver(c, s);
        model_ref _m;
        to_solver_ref(s)->get_model(_m);
        if (!_m) {
            SET_ERROR_CODE(Z3_INVALID_USAGE, "there is no current model");
            RETURN_Z3(nullptr);
        }
        if (_m) {
            model_params mp(to_solver_ref(s)->get_params());
            if (mp.compact()) _m->compress();
        }
        Z3_model_ref * m_ref = alloc(Z3_model_ref, *mk_c(c)); 
        m_ref->m_model = _m;
        mk_c(c)->save_object(m_ref);
        RETURN_Z3(of_model(m_ref));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_solver_get_proof(Z3_context c, Z3_solver s) {
        Z3_TRY;
        LOG_Z3_solver_get_proof(c, s);
        RESET_ERROR_CODE();
        init_solver(c, s);
        proof * p = to_solver_ref(s)->get_proof();
        if (!p) {
            SET_ERROR_CODE(Z3_INVALID_USAGE, "there is no current proof");
            RETURN_Z3(nullptr);
        }
        mk_c(c)->save_ast_trail(p);
        RETURN_Z3(of_ast(p));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast_vector Z3_API Z3_solver_get_unsat_core(Z3_context c, Z3_solver s) {
        Z3_TRY;
        LOG_Z3_solver_get_unsat_core(c, s);
        RESET_ERROR_CODE();
        init_solver(c, s);
        expr_ref_vector core(mk_c(c)->m());
        solver_params sp(to_solver(s)->m_params);
        unsigned timeout     = mk_c(c)->get_timeout();
        timeout              = to_solver(s)->m_params.get_uint("timeout", timeout);
        timeout              = sp.timeout() != UINT_MAX ? sp.timeout() : timeout;
        unsigned rlimit      = to_solver(s)->m_params.get_uint("rlimit", mk_c(c)->get_rlimit());
        bool     use_ctrl_c  = to_solver(s)->m_params.get_bool("ctrl_c", true);
        cancel_eh<reslimit> eh(mk_c(c)->m().limit());
        to_solver(s)->set_eh(&eh);
        {
            scoped_ctrl_c ctrlc(eh, false, use_ctrl_c);
            scoped_timer timer(timeout, &eh);
            scoped_rlimit _rlimit(mk_c(c)->m().limit(), rlimit);
            try {
                to_solver_ref(s)->get_unsat_core(core);
            }
            catch (std::exception& ex) {
                to_solver_ref(s)->set_reason_unknown(eh, ex);
                to_solver(s)->set_eh(nullptr);
                if (core.empty())
                    throw;
            }                    
        }
        to_solver(s)->set_eh(nullptr);
        Z3_ast_vector_ref * v = alloc(Z3_ast_vector_ref, *mk_c(c), mk_c(c)->m());
        mk_c(c)->save_object(v);
        for (expr* e : core) {
            v->m_ast_vector.push_back(e);
        }
        RETURN_Z3(of_ast_vector(v));
        Z3_CATCH_RETURN(nullptr);
    }
    
    Z3_string Z3_API Z3_solver_get_reason_unknown(Z3_context c, Z3_solver s) {
        Z3_TRY;
        LOG_Z3_solver_get_reason_unknown(c, s);
        RESET_ERROR_CODE();
        init_solver(c, s);
        return mk_c(c)->mk_external_string(to_solver_ref(s)->reason_unknown());
        Z3_CATCH_RETURN("");
    }
    
    Z3_stats Z3_API Z3_solver_get_statistics(Z3_context c, Z3_solver s) {
        Z3_TRY;
        LOG_Z3_solver_get_statistics(c, s);
        RESET_ERROR_CODE();
        init_solver(c, s);
        Z3_stats_ref * st = alloc(Z3_stats_ref, *mk_c(c));
        to_solver_ref(s)->collect_statistics(st->m_stats);
        get_memory_statistics(st->m_stats);
        get_rlimit_statistics(mk_c(c)->m().limit(), st->m_stats);
        to_solver_ref(s)->collect_timer_stats(st->m_stats);
        mk_c(c)->save_object(st);
        Z3_stats r = of_stats(st);
        RETURN_Z3(r);
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_string Z3_API Z3_solver_to_string(Z3_context c, Z3_solver s) {
        Z3_TRY;
        LOG_Z3_solver_to_string(c, s);
        RESET_ERROR_CODE();
        init_solver(c, s);
        std::ostringstream buffer;
        to_solver_ref(s)->display(buffer);
        return mk_c(c)->mk_external_string(std::move(buffer).str());
        Z3_CATCH_RETURN("");
    }

    Z3_string Z3_API Z3_solver_to_dimacs_string(Z3_context c, Z3_solver s, bool include_names) {
        Z3_TRY;
        LOG_Z3_solver_to_string(c, s);
        RESET_ERROR_CODE();
        init_solver(c, s);
        std::ostringstream buffer;
        to_solver_ref(s)->display_dimacs(buffer, include_names);
        return mk_c(c)->mk_external_string(std::move(buffer).str());
        Z3_CATCH_RETURN("");
    }


    Z3_lbool Z3_API Z3_get_implied_equalities(Z3_context c, 
                                              Z3_solver s,
                                              unsigned num_terms,
                                              Z3_ast const terms[],
                                              unsigned class_ids[]) {
        Z3_TRY;
        LOG_Z3_get_implied_equalities(c, s, num_terms, terms, class_ids);
        ast_manager& m = mk_c(c)->m();
        RESET_ERROR_CODE();
        init_solver(c, s);
        lbool result = smt::implied_equalities(m, *to_solver_ref(s), num_terms, to_exprs(num_terms, terms), class_ids);
        return static_cast<Z3_lbool>(result); 
        Z3_CATCH_RETURN(Z3_L_UNDEF);
    }

    Z3_lbool Z3_API Z3_solver_get_consequences(Z3_context c, 
                                        Z3_solver s,
                                        Z3_ast_vector assumptions,
                                        Z3_ast_vector variables,
                                        Z3_ast_vector consequences) {
        Z3_TRY;
        LOG_Z3_solver_get_consequences(c, s, assumptions, variables, consequences);
        ast_manager& m = mk_c(c)->m();
        RESET_ERROR_CODE();
        init_solver(c, s);
        expr_ref_vector _assumptions(m), _consequences(m), _variables(m);
        ast_ref_vector const& __assumptions = to_ast_vector_ref(assumptions);
        for (ast* e : __assumptions) {
            if (!is_expr(e)) {
                _assumptions.finalize(); _consequences.finalize(); _variables.finalize();
                SET_ERROR_CODE(Z3_INVALID_USAGE, "assumption is not an expression");
                return Z3_L_UNDEF;
            }
            _assumptions.push_back(to_expr(e));
        }
        ast_ref_vector const& __variables = to_ast_vector_ref(variables);
        for (ast* a : __variables) {
            if (!is_expr(a)) {
                _assumptions.finalize(); _consequences.finalize(); _variables.finalize();
                SET_ERROR_CODE(Z3_INVALID_USAGE, "variable is not an expression");
                return Z3_L_UNDEF;
            }
            _variables.push_back(to_expr(a));
        }
        lbool result = l_undef;
        unsigned timeout     = to_solver(s)->m_params.get_uint("timeout", mk_c(c)->get_timeout());
        unsigned rlimit      = to_solver(s)->m_params.get_uint("rlimit", mk_c(c)->get_rlimit());
        bool     use_ctrl_c  = to_solver(s)->m_params.get_bool("ctrl_c", true);
        cancel_eh<reslimit> eh(mk_c(c)->m().limit());
        to_solver(s)->set_eh(&eh);
        api::context::set_interruptable si(*(mk_c(c)), eh);
        {
            scoped_ctrl_c ctrlc(eh, false, use_ctrl_c);
            scoped_timer timer(timeout, &eh);
            scoped_rlimit _rlimit(mk_c(c)->m().limit(), rlimit);
            try {
                if (to_solver(s)->m_pp) to_solver(s)->m_pp->get_consequences(_assumptions, _variables); 
                result = to_solver_ref(s)->get_consequences(_assumptions, _variables, _consequences);
            }
            catch (z3_exception & ex) {
                to_solver(s)->set_eh(nullptr);
                to_solver_ref(s)->set_reason_unknown(eh, ex);
                _assumptions.finalize(); _consequences.finalize(); _variables.finalize();
                mk_c(c)->handle_exception(ex);
                return Z3_L_UNDEF;
            }
            catch (...) {
            }
        }
        to_solver(s)->set_eh(nullptr);
        if (result == l_undef) {
            to_solver_ref(s)->set_reason_unknown(eh, __FILE__ ":" TOSTRING(__LINE__));
        }
        for (expr* e : _consequences) {
            to_ast_vector_ref(consequences).push_back(e);
        }
        return static_cast<Z3_lbool>(result); 
        Z3_CATCH_RETURN(Z3_L_UNDEF);        
    }

    Z3_ast_vector Z3_API Z3_solver_cube(Z3_context c, Z3_solver s, Z3_ast_vector vs, unsigned cutoff) {
        Z3_TRY;
        LOG_Z3_solver_cube(c, s, vs, cutoff);
        ast_manager& m = mk_c(c)->m();
        expr_ref_vector result(m), vars(m);
        for (ast* a : to_ast_vector_ref(vs)) {
            if (!is_expr(a)) {
                SET_ERROR_CODE(Z3_INVALID_USAGE, "cube contains a non-expression");
            }
            else {
                vars.push_back(to_expr(a));
            }
        }
        unsigned timeout     = to_solver(s)->m_params.get_uint("timeout", mk_c(c)->get_timeout());
        unsigned rlimit      = to_solver(s)->m_params.get_uint("rlimit", mk_c(c)->get_rlimit());
        bool     use_ctrl_c  = to_solver(s)->m_params.get_bool("ctrl_c", true);
        cancel_eh<reslimit> eh(mk_c(c)->m().limit());
        to_solver(s)->set_eh(&eh);
        api::context::set_interruptable si(*(mk_c(c)), eh);
        {
            scoped_ctrl_c ctrlc(eh, false, use_ctrl_c);
            scoped_timer timer(timeout, &eh);
            scoped_rlimit _rlimit(mk_c(c)->m().limit(), rlimit);
            try {
                result.append(to_solver_ref(s)->cube(vars, cutoff));
            }
            catch (z3_exception & ex) {
                to_solver(s)->set_eh(nullptr);
                mk_c(c)->handle_exception(ex);
                return nullptr;
            }
            catch (...) {
            }
        }
        to_solver(s)->set_eh(nullptr);
        Z3_ast_vector_ref * v = alloc(Z3_ast_vector_ref, *mk_c(c), mk_c(c)->m());
        mk_c(c)->save_object(v);
        for (expr* e : result) {
            v->m_ast_vector.push_back(e);
        }
        to_ast_vector_ref(vs).reset();
        for (expr* a : vars) {
            to_ast_vector_ref(vs).push_back(a);
        }
        RETURN_Z3(of_ast_vector(v));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_solver_congruence_root(Z3_context c, Z3_solver s, Z3_ast a) {
        Z3_TRY;
        LOG_Z3_solver_congruence_root(c, s, a);
        RESET_ERROR_CODE();
        init_solver(c, s);
        expr* r = to_solver_ref(s)->congruence_root(to_expr(a));
        RETURN_Z3(of_expr(r));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_solver_congruence_next(Z3_context c, Z3_solver s, Z3_ast a) {
        Z3_TRY;
        LOG_Z3_solver_congruence_next(c, s, a);
        RESET_ERROR_CODE();
        init_solver(c, s);
        expr* sib = to_solver_ref(s)->congruence_next(to_expr(a));
        RETURN_Z3(of_expr(sib));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_solver_congruence_explain(Z3_context c, Z3_solver s, Z3_ast a, Z3_ast b) {
        Z3_TRY;
        LOG_Z3_solver_congruence_explain(c, s, a, b);
        RESET_ERROR_CODE();
        init_solver(c, s);
        auto exp = to_solver_ref(s)->congruence_explain(to_expr(a), to_expr(b));
        mk_c(c)->save_ast_trail(exp.get());
        RETURN_Z3(of_expr(exp));
        Z3_CATCH_RETURN(nullptr);
    }

    void Z3_API Z3_solver_solve_for(Z3_context c, Z3_solver s, Z3_ast_vector vars, Z3_ast_vector terms, Z3_ast_vector guards) {
        Z3_TRY;
        LOG_Z3_solver_solve_for(c, s, vars, terms, guards);
        RESET_ERROR_CODE();
        init_solver(c, s);
        ast_manager& m = mk_c(c)->m();
        auto& _vars = to_ast_vector_ref(vars);
        auto& _terms = to_ast_vector_ref(terms);
        auto& _guards = to_ast_vector_ref(guards);
        vector<solver::solution> solutions;
        for (auto t : _vars) 
            solutions.push_back({ to_expr(t), expr_ref(m), expr_ref(m) });        
        to_solver_ref(s)->solve_for(solutions);
        _vars.reset();
        _terms.reset();
        _guards.reset();
        for (solver::solution const& s : solutions) {
            if (!s.term)
                continue;
            _vars.push_back(s.var);
            _terms.push_back(s.term);
            _guards.push_back(s.guard ? s.guard : m.mk_true());
        }
        Z3_CATCH;
    }

    class api_context_obj : public user_propagator::context_obj {
        api::context* c;
    public:
        api_context_obj(api::context* c):c(c) {}
        ~api_context_obj() override { dealloc(c); }
    };

    struct scoped_ast_vector {
        Z3_ast_vector_ref* v;
        scoped_ast_vector(Z3_ast_vector_ref* v): v(v) { v->inc_ref(); }
        ~scoped_ast_vector() { v->dec_ref(); }
    };

    void Z3_API Z3_solver_register_on_clause(
        Z3_context  c, 
        Z3_solver   s, 
        void*       user_context,
        Z3_on_clause_eh on_clause_eh) {
        Z3_TRY;
        RESET_ERROR_CODE();
        init_solver(c, s);     
        user_propagator::on_clause_eh_t _on_clause = [=](void* user_ctx, expr* proof, unsigned nd, unsigned const* deps, unsigned n, expr* const* _literals) {
            Z3_ast_vector_ref * literals = alloc(Z3_ast_vector_ref, *mk_c(c), mk_c(c)->m());
            mk_c(c)->save_object(literals);
            expr_ref pr(proof, mk_c(c)->m());
            scoped_ast_vector _sc(literals);
            for (unsigned i = 0; i < n; ++i)
                literals->m_ast_vector.push_back(_literals[i]);
            on_clause_eh(user_ctx, of_expr(pr.get()), nd, deps, of_ast_vector(literals));
        };
        to_solver_ref(s)->register_on_clause(user_context, _on_clause);
        auto& solver = *to_solver(s);

        if (!solver.m_cmd_context) {
            solver.m_cmd_context = alloc(cmd_context, false, &(mk_c(c)->m()));
            install_proof_cmds(*solver.m_cmd_context);            
        }

        if (!solver.m_cmd_context->get_proof_cmds()) {
            init_proof_cmds(*solver.m_cmd_context);
            solver.m_cmd_context->get_proof_cmds()->updt_params(solver.m_params);            
        }
        solver.m_cmd_context->get_proof_cmds()->register_on_clause(user_context, _on_clause);
        Z3_CATCH;   
    }

    void Z3_API Z3_solver_propagate_init(
        Z3_context  c, 
        Z3_solver   s, 
        void*       user_context,
        Z3_push_eh  push_eh,
        Z3_pop_eh   pop_eh,
        Z3_fresh_eh fresh_eh) {
        Z3_TRY;
        RESET_ERROR_CODE();
        init_solver(c, s);
        user_propagator::push_eh_t _push = (void(*)(void*,user_propagator::callback*)) push_eh;
        user_propagator::pop_eh_t _pop = (void(*)(void*,user_propagator::callback*,unsigned)) pop_eh;
        user_propagator::fresh_eh_t _fresh = [=](void * user_ctx, ast_manager& m, user_propagator::context_obj*& _ctx) {
            ast_context_params params;
            params.set_foreign_manager(&m);
            auto* ctx = alloc(api::context, &params, false);
            _ctx = alloc(api_context_obj, ctx);
            return fresh_eh(user_ctx, reinterpret_cast<Z3_context>(ctx));
        };
        to_solver_ref(s)->user_propagate_init(user_context, _push, _pop, _fresh);
        Z3_CATCH;
    }

    void Z3_API Z3_solver_propagate_fixed(
        Z3_context  c, 
        Z3_solver   s,
        Z3_fixed_eh fixed_eh) {
        Z3_TRY;
        RESET_ERROR_CODE();
        user_propagator::fixed_eh_t _fixed = (void(*)(void*,user_propagator::callback*,expr*,expr*))fixed_eh;
        to_solver_ref(s)->user_propagate_register_fixed(_fixed);
        Z3_CATCH;        
    }

    void Z3_API Z3_solver_propagate_final(
        Z3_context  c, 
        Z3_solver   s,
        Z3_final_eh final_eh) {
        Z3_TRY;
        RESET_ERROR_CODE();
        user_propagator::final_eh_t _final = (bool(*)(void*,user_propagator::callback*))final_eh;
        to_solver_ref(s)->user_propagate_register_final(_final);
        Z3_CATCH;        
    }

    void Z3_API Z3_solver_propagate_eq(
        Z3_context  c, 
        Z3_solver   s,
        Z3_eq_eh eq_eh) {
        Z3_TRY;
        RESET_ERROR_CODE();
        user_propagator::eq_eh_t _eq = (void(*)(void*,user_propagator::callback*,expr*,expr*))eq_eh;
        to_solver_ref(s)->user_propagate_register_eq(_eq);
        Z3_CATCH;        
    }

    void Z3_API Z3_solver_propagate_diseq(
        Z3_context  c, 
        Z3_solver   s,
        Z3_eq_eh    diseq_eh) {
        Z3_TRY;
        RESET_ERROR_CODE();
        user_propagator::eq_eh_t _diseq = (void(*)(void*,user_propagator::callback*,expr*,expr*))diseq_eh;
        to_solver_ref(s)->user_propagate_register_diseq(_diseq);
        Z3_CATCH;        
    }

    void Z3_API Z3_solver_propagate_register(Z3_context c, Z3_solver s, Z3_ast e) {
        Z3_TRY;
        LOG_Z3_solver_propagate_register(c, s, e);
        RESET_ERROR_CODE();
        to_solver_ref(s)->user_propagate_register_expr(to_expr(e));
        Z3_CATCH;        
    }

    void Z3_API Z3_solver_propagate_register_cb(Z3_context c, Z3_solver_callback s, Z3_ast e) {
        Z3_TRY;
        LOG_Z3_solver_propagate_register_cb(c, s, e);
        RESET_ERROR_CODE();
        reinterpret_cast<user_propagator::callback*>(s)->register_cb(to_expr(e));
        Z3_CATCH;
    }

    bool Z3_API Z3_solver_propagate_consequence(Z3_context c, Z3_solver_callback s, unsigned num_fixed, Z3_ast const* fixed_ids, unsigned num_eqs, Z3_ast const* eq_lhs, Z3_ast const* eq_rhs, Z3_ast conseq) {
        Z3_TRY;
        LOG_Z3_solver_propagate_consequence(c, s, num_fixed, fixed_ids, num_eqs, eq_lhs, eq_rhs, conseq);
        RESET_ERROR_CODE();
        expr* const * _fixed_ids = (expr* const*) fixed_ids;
        expr* const * _eq_lhs = (expr*const*) eq_lhs;
        expr* const * _eq_rhs = (expr*const*) eq_rhs;
        return reinterpret_cast<user_propagator::callback*>(s)->propagate_cb(num_fixed, _fixed_ids, num_eqs, _eq_lhs, _eq_rhs, to_expr(conseq));
        Z3_CATCH_RETURN(false);
    }

    void Z3_API Z3_solver_propagate_created(Z3_context c, Z3_solver s, Z3_created_eh created_eh) {
        Z3_TRY;
        RESET_ERROR_CODE();
        user_propagator::created_eh_t c = (void(*)(void*, user_propagator::callback*, expr*))created_eh;
        to_solver_ref(s)->user_propagate_register_created(c);
        Z3_CATCH;
    }

    void Z3_API Z3_solver_propagate_decide(Z3_context c, Z3_solver s, Z3_decide_eh decide_eh) {
        Z3_TRY;
        RESET_ERROR_CODE();
        user_propagator::decide_eh_t c = (void(*)(void*, user_propagator::callback*, expr*, unsigned, bool))decide_eh;
        to_solver_ref(s)->user_propagate_register_decide(c);
        Z3_CATCH;
    }

    bool Z3_API Z3_solver_next_split(Z3_context c, Z3_solver_callback cb,  Z3_ast t, unsigned idx, Z3_lbool phase) {
        Z3_TRY;
        LOG_Z3_solver_next_split(c, cb, t, idx, phase);
        RESET_ERROR_CODE();
        return reinterpret_cast<user_propagator::callback*>(cb)->next_split_cb(to_expr(t), idx, (lbool)phase);
        Z3_CATCH_RETURN(false);
    }

    Z3_func_decl Z3_API Z3_solver_propagate_declare(Z3_context c, Z3_symbol name, unsigned n, Z3_sort* domain, Z3_sort range) {
        Z3_TRY;
        LOG_Z3_solver_propagate_declare(c, name, n, domain, range);
        RESET_ERROR_CODE();
        ast_manager& m = mk_c(c)->m();        
        family_id fid = m.mk_family_id(user_propagator::plugin::name());
        if (!m.has_plugin(fid)) 
            m.register_plugin(fid, alloc(user_propagator::plugin));            
        func_decl_info info(fid, user_propagator::plugin::kind_t::OP_USER_PROPAGATE);
        func_decl* f = m.mk_func_decl(to_symbol(name), n, to_sorts(domain), to_sort(range), info);
        mk_c(c)->save_ast_trail(f);
        RETURN_Z3(of_func_decl(f));
        Z3_CATCH_RETURN(nullptr);
    }

    void Z3_API Z3_solver_set_initial_value(Z3_context c, Z3_solver s, Z3_ast var, Z3_ast value) {
        Z3_TRY;
        LOG_Z3_solver_set_initial_value(c, s, var, value);
        RESET_ERROR_CODE();
        init_solver(c, s);
        if (to_expr(var)->get_sort() != to_expr(value)->get_sort()) {
            SET_ERROR_CODE(Z3_INVALID_USAGE, "variable and value should have same sort");
            return;
        }
        ast_manager& m = mk_c(c)->m();
        if (!m.is_value(to_expr(value))) {
            SET_ERROR_CODE(Z3_INVALID_USAGE, "a proper value was not supplied");
            return;
        }
        to_solver_ref(s)->user_propagate_initialize_value(to_expr(var), to_expr(value));
        Z3_CATCH;        
    }



};
