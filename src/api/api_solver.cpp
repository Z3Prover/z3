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
#include<iostream>
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
#include "solver/solver_params.hpp"
#include "cmd_context/cmd_context.h"
#include "parsers/smt2/smt2parser.h"
#include "sat/dimacs.h"
#include "sat/sat_solver.h"
#include "sat/tactic/goal2sat.h"


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
        m_out << "(push)\n";
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
        m_out << "(check-sat";        
        for (unsigned i = 0; i < n; ++i) {
            m_pp_util.display_expr(m_out << "\n", asms[i]);            
        }
        for (expr* e : m_tracked) {
            m_pp_util.display_expr(m_out << "\n", e);
        }
        m_out << ")\n";
        m_out.flush();
    }

    void solver2smt2_pp::get_consequences(expr_ref_vector const& assumptions, expr_ref_vector const& variables) {
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
        m_out << ")\n";
        m_out.flush();
    }

    solver2smt2_pp::solver2smt2_pp(ast_manager& m, char const* file): 
        m_pp_util(m), m_out(file), m_tracked(m) {
        if (!m_out) {
            throw default_exception("could not open " + std::string(file) + " for output");
        }
    }

    void Z3_solver_ref::set_eh(event_handler* eh) {
        std::lock_guard<std::mutex> lock(m_mux);
        m_eh = eh;
    }

    void Z3_solver_ref::set_cancel() {
        std::lock_guard<std::mutex> lock(m_mux);
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
        bool proofs_enabled, models_enabled, unsat_core_enabled;
        params_ref p = s->m_params;
        mk_c(c)->params().get_solver_params(mk_c(c)->m(), p, proofs_enabled, models_enabled, unsat_core_enabled);
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

    Z3_solver Z3_API Z3_mk_simple_solver(Z3_context c) {
        Z3_TRY;
        LOG_Z3_mk_simple_solver(c);
        RESET_ERROR_CODE();
        Z3_solver_ref * s = alloc(Z3_solver_ref, *mk_c(c), mk_smt_solver_factory());
        mk_c(c)->save_object(s);
        Z3_solver r = of_solver(s);
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
            throw default_exception(strm.str());
            RETURN_Z3(nullptr);
        }
        else {
            Z3_solver_ref * s = alloc(Z3_solver_ref, *mk_c(c), mk_smt_strategic_solver_factory(to_symbol(logic)));
            mk_c(c)->save_object(s);
            Z3_solver r = of_solver(s);
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
        RETURN_Z3(r);
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_solver Z3_API Z3_solver_translate(Z3_context c, Z3_solver s, Z3_context target) {
        Z3_TRY;
        LOG_Z3_solver_translate(c, s, target);
        RESET_ERROR_CODE();
        params_ref const& p = to_solver(s)->m_params; 
        Z3_solver_ref * sr = alloc(Z3_solver_ref, *mk_c(target), nullptr);
        init_solver(c, s);
        sr->m_solver = to_solver(s)->m_solver->translate(mk_c(target)->m(), p);
        mk_c(target)->save_object(sr);
        Z3_solver r = of_solver(sr);
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
        scoped_ptr<cmd_context> ctx = alloc(cmd_context, false, &(mk_c(c)->m()));
        ctx->set_ignore_check(true);
        std::stringstream errstrm;
        ctx->set_regular_stream(errstrm);

        if (!parse_smt2_commands(*ctx.get(), is)) {
            ctx = nullptr;
            SET_ERROR_CODE(Z3_PARSER_ERROR, errstrm.str().c_str());
            return;
        }

        bool initialized = to_solver(s)->m_solver.get() != nullptr;
        if (!initialized)
            init_solver(c, s);
        for (expr * e : ctx->assertions()) {
            to_solver(s)->assert_expr(e);
        }
        to_solver_ref(s)->set_model_converter(ctx->get_model_converter());
    }

    static void solver_from_dimacs_stream(Z3_context c, Z3_solver s, std::istream& is) {
        init_solver(c, s);
        ast_manager& m = to_solver_ref(s)->get_manager();
        std::stringstream err;
        sat::solver solver(to_solver_ref(s)->get_params(), m.limit());
        if (!parse_dimacs(is, err, solver)) {
            SET_ERROR_CODE(Z3_PARSER_ERROR, err.str().c_str());
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
        std::string str(c_str);
        std::istringstream is(str);
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
        return mk_c(c)->mk_external_string(buffer.str());
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

        symbol logic = to_param_ref(p).get_sym("smt.logic", symbol::null);
        symbol smt2log = to_param_ref(p).get_sym("solver.smtlib2_log", symbol::null);
        if (logic != symbol::null) {
            to_solver(s)->m_logic = logic;
        }
        if (smt2log != symbol::null && !to_solver(s)->m_pp) {
            to_solver(s)->m_pp = alloc(solver2smt2_pp, mk_c(c)->m(), smt2log.str().c_str());
        }
        if (to_solver(s)->m_solver) {
            bool old_model = to_solver(s)->m_params.get_bool("model", true);
            bool new_model = to_param_ref(p).get_bool("model", true);
            if (old_model != new_model)
                to_solver_ref(s)->set_produce_models(new_model);
            param_descrs r;
            to_solver_ref(s)->collect_param_descrs(r);
            context_params::collect_solver_param_descrs(r);
            to_param_ref(p).validate(r);
            to_solver_ref(s)->updt_params(to_param_ref(p));
        }
        to_solver(s)->m_params.append(to_param_ref(p));
        
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
        RESET_ERROR_CODE();
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
        expr_ref_vector trail = to_solver_ref(s)->get_trail();
        for (expr* f : trail) {
            v->m_ast_vector.push_back(f);
        }
        RETURN_Z3(of_ast_vector(v));
        Z3_CATCH_RETURN(nullptr);
    }

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
                to_solver_ref(s)->set_reason_unknown(eh);
                to_solver(s)->set_eh(nullptr);
                if (!mk_c(c)->m().canceled()) {
                    mk_c(c)->handle_exception(ex);
                }
                return Z3_L_UNDEF;
            }
            catch (...) {
                to_solver_ref(s)->set_reason_unknown(eh);
                to_solver(s)->set_eh(nullptr);
                return Z3_L_UNDEF;
            }
        }
        to_solver(s)->set_eh(nullptr);
        if (result == l_undef) {
            to_solver_ref(s)->set_reason_unknown(eh);
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
        to_solver_ref(s)->get_unsat_core(core);
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
        return mk_c(c)->mk_external_string(buffer.str());
        Z3_CATCH_RETURN("");
    }

    Z3_string Z3_API Z3_solver_to_dimacs_string(Z3_context c, Z3_solver s) {
        Z3_TRY;
        LOG_Z3_solver_to_string(c, s);
        RESET_ERROR_CODE();
        init_solver(c, s);
        std::ostringstream buffer;
        to_solver_ref(s)->display_dimacs(buffer);
        return mk_c(c)->mk_external_string(buffer.str());
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
        CHECK_SEARCHING(c);
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
        CHECK_SEARCHING(c);
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
                to_solver_ref(s)->set_reason_unknown(eh);
                _assumptions.finalize(); _consequences.finalize(); _variables.finalize();
                mk_c(c)->handle_exception(ex);
                return Z3_L_UNDEF;
            }
            catch (...) {
            }
        }
        to_solver(s)->set_eh(nullptr);
        if (result == l_undef) {
            to_solver_ref(s)->set_reason_unknown(eh);
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


};
