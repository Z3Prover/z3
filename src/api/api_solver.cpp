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
#include "api/z3.h"
#include "api/api_log_macros.h"
#include "api/api_context.h"
#include "api/api_tactic.h"
#include "api/api_solver.h"
#include "api/api_model.h"
#include "api/api_stats.h"
#include "api/api_ast_vector.h"
#include "solver/tactic2solver.h"
#include "util/scoped_ctrl_c.h"
#include "util/cancel_eh.h"
#include "util/file_path.h"
#include "util/scoped_timer.h"
#include "tactic/portfolio/smt_strategic_solver.h"
#include "smt/smt_solver.h"
#include "smt/smt_implied_equalities.h"
#include "solver/smt_logics.h"
#include "cmd_context/cmd_context.h"
#include "parsers/smt2/smt2parser.h"
#include "sat/dimacs.h"
#include "sat/sat_solver.h"
#include "sat/tactic/goal2sat.h"

extern "C" {

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
        if (to_solver(s)->m_solver.get() == 0)
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
        Z3_CATCH_RETURN(0);
    }

    Z3_solver Z3_API Z3_mk_solver(Z3_context c) {
        Z3_TRY;
        LOG_Z3_mk_solver(c);
        RESET_ERROR_CODE();
        Z3_solver_ref * s = alloc(Z3_solver_ref, *mk_c(c), mk_smt_strategic_solver_factory());
        mk_c(c)->save_object(s);
        Z3_solver r = of_solver(s);
        RETURN_Z3(r);
        Z3_CATCH_RETURN(0);
    }

    Z3_solver Z3_API Z3_mk_solver_for_logic(Z3_context c, Z3_symbol logic) {
        Z3_TRY;
        LOG_Z3_mk_solver_for_logic(c, logic);
        RESET_ERROR_CODE();
        if (!smt_logics::supported_logic(to_symbol(logic))) {
            std::ostringstream strm;
            strm << "logic '" << to_symbol(logic) << "' is not recognized";
            throw default_exception(strm.str());
            RETURN_Z3(0);
        }
        else {
            Z3_solver_ref * s = alloc(Z3_solver_ref, *mk_c(c), mk_smt_strategic_solver_factory(to_symbol(logic)));
            mk_c(c)->save_object(s);
            Z3_solver r = of_solver(s);
            RETURN_Z3(r);
        }
        Z3_CATCH_RETURN(0);
    }

    Z3_solver Z3_API Z3_mk_solver_from_tactic(Z3_context c, Z3_tactic t) {
        Z3_TRY;
        LOG_Z3_mk_solver_from_tactic(c, t);
        RESET_ERROR_CODE();
        Z3_solver_ref * s = alloc(Z3_solver_ref, *mk_c(c), mk_tactic2solver_factory(to_tactic_ref(t)));
        mk_c(c)->save_object(s);
        Z3_solver r = of_solver(s);
        RETURN_Z3(r);
        Z3_CATCH_RETURN(0);
    }

    Z3_solver Z3_API Z3_solver_translate(Z3_context c, Z3_solver s, Z3_context target) {
        Z3_TRY;
        LOG_Z3_solver_translate(c, s, target);
        RESET_ERROR_CODE();
        params_ref const& p = to_solver(s)->m_params; 
        Z3_solver_ref * sr = alloc(Z3_solver_ref, *mk_c(target), 0);
        init_solver(c, s);
        sr->m_solver = to_solver(s)->m_solver->translate(mk_c(target)->m(), p);
        mk_c(target)->save_object(sr);
        Z3_solver r = of_solver(sr);
        RETURN_Z3(r);
        Z3_CATCH_RETURN(0);
    }

    void solver_from_stream(Z3_context c, Z3_solver s, std::istream& is) {
        scoped_ptr<cmd_context> ctx = alloc(cmd_context, false, &(mk_c(c)->m()));
        ctx->set_ignore_check(true);

        if (!parse_smt2_commands(*ctx.get(), is)) {
            ctx = nullptr;
            SET_ERROR_CODE(Z3_PARSER_ERROR);
            return;
        }

        bool initialized = to_solver(s)->m_solver.get() != 0;
        if (!initialized)
            init_solver(c, s);
        ptr_vector<expr>::const_iterator it  = ctx->begin_assertions();
        ptr_vector<expr>::const_iterator end = ctx->end_assertions();
        for (; it != end; ++it) {
            to_solver_ref(s)->assert_expr(*it);
        }
        // to_solver_ref(s)->set_model_converter(ctx->get_model_converter());
    }

    void Z3_API Z3_solver_from_string(Z3_context c, Z3_solver s, Z3_string c_str) {
        Z3_TRY;
        LOG_Z3_solver_from_string(c, s, c_str);
        std::string str(c_str);
        std::istringstream is(str);
        solver_from_stream(c, s, is);
        Z3_CATCH;        
    }

    void Z3_API Z3_solver_from_file(Z3_context c, Z3_solver s, Z3_string file_name) {
        Z3_TRY;
        LOG_Z3_solver_from_file(c, s, file_name);
        char const* ext = get_extension(file_name);
        std::ifstream is(file_name);
        if (!is) {
            SET_ERROR_CODE(Z3_FILE_ACCESS_ERROR);
        }
        else if (ext && std::string("dimacs") == ext) {
            ast_manager& m = to_solver_ref(s)->get_manager();
            sat::solver solver(to_solver_ref(s)->get_params(), m.limit(), nullptr);
            parse_dimacs(is, solver);
            sat2goal s2g;
            model_converter_ref mc;
            atom2bool_var a2b(m);
            goal g(m);            
            s2g(solver, a2b, to_solver_ref(s)->get_params(), g, mc);
            for (unsigned i = 0; i < g.size(); ++i) {
                to_solver_ref(s)->assert_expr(g.form(i));
            }
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
        bool initialized = to_solver(s)->m_solver.get() != 0;
        if (!initialized)
            init_solver(c, s);
        to_solver_ref(s)->collect_param_descrs(descrs);
        context_params::collect_solver_param_descrs(descrs);
        if (!initialized)
            to_solver(s)->m_solver = 0;
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
        bool initialized = to_solver(s)->m_solver.get() != 0;
        if (!initialized)
            init_solver(c, s);
        to_solver_ref(s)->collect_param_descrs(d->m_descrs);
        context_params::collect_solver_param_descrs(d->m_descrs);
        if (!initialized)
            to_solver(s)->m_solver = 0;
        Z3_param_descrs r = of_param_descrs(d);
        RETURN_Z3(r);
        Z3_CATCH_RETURN(0);
    }

    void Z3_API Z3_solver_set_params(Z3_context c, Z3_solver s, Z3_params p) {
        Z3_TRY;
        LOG_Z3_solver_set_params(c, s, p);
        RESET_ERROR_CODE();

        symbol logic = to_param_ref(p).get_sym("smt.logic", symbol::null);
        if (logic != symbol::null) {
            to_solver(s)->m_logic = logic;
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
        Z3_CATCH;
    }

    void Z3_API Z3_solver_pop(Z3_context c, Z3_solver s, unsigned n) {
        Z3_TRY;
        LOG_Z3_solver_pop(c, s, n);
        RESET_ERROR_CODE();
        init_solver(c, s);
        if (n > to_solver_ref(s)->get_scope_level()) {
            SET_ERROR_CODE(Z3_IOB);
            return;
        }
        if (n > 0)
            to_solver_ref(s)->pop(n);
        Z3_CATCH;
    }

    void Z3_API Z3_solver_reset(Z3_context c, Z3_solver s) {
        Z3_TRY;
        LOG_Z3_solver_reset(c, s);
        RESET_ERROR_CODE();
        to_solver(s)->m_solver = 0;
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
        to_solver_ref(s)->assert_expr(to_expr(a));
        Z3_CATCH;
    }

    void Z3_API Z3_solver_assert_and_track(Z3_context c, Z3_solver s, Z3_ast a, Z3_ast p) {
        Z3_TRY;
        LOG_Z3_solver_assert_and_track(c, s, a, p);
        RESET_ERROR_CODE();
        init_solver(c, s);
        CHECK_FORMULA(a,);
        CHECK_FORMULA(p,);
        to_solver_ref(s)->assert_expr(to_expr(a), to_expr(p));
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
        Z3_CATCH_RETURN(0);
    }

    static Z3_lbool _solver_check(Z3_context c, Z3_solver s, unsigned num_assumptions, Z3_ast const assumptions[]) {
        for (unsigned i = 0; i < num_assumptions; i++) {
            if (!is_expr(to_ast(assumptions[i]))) {
                SET_ERROR_CODE(Z3_INVALID_ARG);
                return Z3_L_UNDEF;
            }
        }
        expr * const * _assumptions = to_exprs(assumptions);
        unsigned timeout     = to_solver(s)->m_params.get_uint("timeout", mk_c(c)->get_timeout());
        unsigned rlimit      = to_solver(s)->m_params.get_uint("rlimit", mk_c(c)->get_rlimit());
        bool     use_ctrl_c  = to_solver(s)->m_params.get_bool("ctrl_c", false);
        cancel_eh<reslimit> eh(mk_c(c)->m().limit());
        api::context::set_interruptable si(*(mk_c(c)), eh);
        lbool result;
        {
            scoped_ctrl_c ctrlc(eh, false, use_ctrl_c);
            scoped_timer timer(timeout, &eh);
            scoped_rlimit _rlimit(mk_c(c)->m().limit(), rlimit);
            try {
                result = to_solver_ref(s)->check_sat(num_assumptions, _assumptions);
            }
            catch (z3_exception & ex) {
                to_solver_ref(s)->set_reason_unknown(eh);
                mk_c(c)->handle_exception(ex);
                return Z3_L_UNDEF;
            }
        }
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
        return _solver_check(c, s, 0, 0);
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
            SET_ERROR_CODE(Z3_INVALID_USAGE);
            RETURN_Z3(0);
        }
        Z3_model_ref * m_ref = alloc(Z3_model_ref, *mk_c(c)); 
        m_ref->m_model = _m;
        mk_c(c)->save_object(m_ref);
        RETURN_Z3(of_model(m_ref));
        Z3_CATCH_RETURN(0);
    }

    Z3_ast Z3_API Z3_solver_get_proof(Z3_context c, Z3_solver s) {
        Z3_TRY;
        LOG_Z3_solver_get_proof(c, s);
        RESET_ERROR_CODE();
        init_solver(c, s);
        proof * p = to_solver_ref(s)->get_proof();
        if (!p) {
            SET_ERROR_CODE(Z3_INVALID_USAGE);
            RETURN_Z3(0);
        }
        mk_c(c)->save_ast_trail(p);
        RETURN_Z3(of_ast(p));
        Z3_CATCH_RETURN(0);
    }

    Z3_ast_vector Z3_API Z3_solver_get_unsat_core(Z3_context c, Z3_solver s) {
        Z3_TRY;
        LOG_Z3_solver_get_unsat_core(c, s);
        RESET_ERROR_CODE();
        init_solver(c, s);
        ptr_vector<expr> core;
        to_solver_ref(s)->get_unsat_core(core);
        Z3_ast_vector_ref * v = alloc(Z3_ast_vector_ref, *mk_c(c), mk_c(c)->m());
        mk_c(c)->save_object(v);
        for (unsigned i = 0; i < core.size(); i++) {
            v->m_ast_vector.push_back(core[i]);
        }
        RETURN_Z3(of_ast_vector(v));
        Z3_CATCH_RETURN(0);
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
        Z3_CATCH_RETURN(0);
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
        lbool result = smt::implied_equalities(m, *to_solver_ref(s), num_terms, to_exprs(terms), class_ids);
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
        unsigned sz = __assumptions.size();
        for (unsigned i = 0; i < sz; ++i) {
            if (!is_expr(__assumptions[i])) {
                _assumptions.finalize(); _consequences.finalize(); _variables.finalize();
                SET_ERROR_CODE(Z3_INVALID_USAGE);
                return Z3_L_UNDEF;
            }
            _assumptions.push_back(to_expr(__assumptions[i]));
        }
        ast_ref_vector const& __variables = to_ast_vector_ref(variables);
        sz = __variables.size();
        for (unsigned i = 0; i < sz; ++i) {
            if (!is_expr(__variables[i])) {
                _assumptions.finalize(); _consequences.finalize(); _variables.finalize();
                SET_ERROR_CODE(Z3_INVALID_USAGE);
                return Z3_L_UNDEF;
            }
            _variables.push_back(to_expr(__variables[i]));
        }
        lbool result = l_undef;
        unsigned timeout     = to_solver(s)->m_params.get_uint("timeout", mk_c(c)->get_timeout());
        unsigned rlimit      = to_solver(s)->m_params.get_uint("rlimit", mk_c(c)->get_rlimit());
        bool     use_ctrl_c  = to_solver(s)->m_params.get_bool("ctrl_c", false);
        cancel_eh<reslimit> eh(mk_c(c)->m().limit());
        api::context::set_interruptable si(*(mk_c(c)), eh);
        {
            scoped_ctrl_c ctrlc(eh, false, use_ctrl_c);
            scoped_timer timer(timeout, &eh);
            scoped_rlimit _rlimit(mk_c(c)->m().limit(), rlimit);
            try {
                result = to_solver_ref(s)->get_consequences(_assumptions, _variables, _consequences);
            }
            catch (z3_exception & ex) {
                to_solver_ref(s)->set_reason_unknown(eh);
                _assumptions.finalize(); _consequences.finalize(); _variables.finalize();
                mk_c(c)->handle_exception(ex);
                return Z3_L_UNDEF;
            }
        }
        if (result == l_undef) {
            to_solver_ref(s)->set_reason_unknown(eh);
        }
        for (unsigned i = 0; i < _consequences.size(); ++i) {
            to_ast_vector_ref(consequences).push_back(_consequences[i].get());
        }
        return static_cast<Z3_lbool>(result); 
        Z3_CATCH_RETURN(Z3_L_UNDEF);        
    }

};
