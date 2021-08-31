/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    api_opt.cpp

Abstract:
    API for optimization 

Author:

    Nikolaj Bjorner (nbjorner) 2013-12-3.

Revision History:

--*/
#include<iostream>
#include "util/cancel_eh.h"
#include "util/scoped_timer.h"
#include "util/scoped_ctrl_c.h"
#include "util/file_path.h"
#include "parsers/smt2/smt2parser.h"
#include "model/model_params.hpp"
#include "opt/opt_context.h"
#include "opt/opt_cmds.h"
#include "opt/opt_parse.h"
#include "api/z3.h"
#include "api/api_log_macros.h"
#include "api/api_stats.h"
#include "api/api_context.h"
#include "api/api_util.h"
#include "api/api_model.h"
#include "api/api_ast_vector.h"


extern "C" {

    struct Z3_optimize_ref : public api::object {
        opt::context* m_opt;
        Z3_optimize_ref(api::context& c): api::object(c), m_opt(nullptr) {}
        ~Z3_optimize_ref() override { dealloc(m_opt); }
    };
    inline Z3_optimize_ref * to_optimize(Z3_optimize o) { return reinterpret_cast<Z3_optimize_ref *>(o); }
    inline Z3_optimize of_optimize(Z3_optimize_ref * o) { return reinterpret_cast<Z3_optimize>(o); }
    inline opt::context* to_optimize_ptr(Z3_optimize o) { return to_optimize(o)->m_opt; }

    Z3_optimize Z3_API Z3_mk_optimize(Z3_context c) {
        Z3_TRY;
        LOG_Z3_mk_optimize(c);
        RESET_ERROR_CODE();
        Z3_optimize_ref * o = alloc(Z3_optimize_ref, *mk_c(c));
        o->m_opt = alloc(opt::context,mk_c(c)->m());
        mk_c(c)->save_object(o);
        RETURN_Z3(of_optimize(o));
        Z3_CATCH_RETURN(nullptr);
    }

    void Z3_API Z3_optimize_inc_ref(Z3_context c, Z3_optimize o) {
        Z3_TRY;
        LOG_Z3_optimize_inc_ref(c, o);
        RESET_ERROR_CODE();
        to_optimize(o)->inc_ref();
        Z3_CATCH;
    }

    void Z3_API Z3_optimize_dec_ref(Z3_context c, Z3_optimize o) {
        Z3_TRY;
        LOG_Z3_optimize_dec_ref(c, o);
        RESET_ERROR_CODE();
        if (o)
            to_optimize(o)->dec_ref();
        Z3_CATCH;
    }
    
    void Z3_API Z3_optimize_assert(Z3_context c, Z3_optimize o, Z3_ast a) {
        Z3_TRY;
        LOG_Z3_optimize_assert(c, o, a);
        RESET_ERROR_CODE();
        CHECK_FORMULA(a,);        
        to_optimize_ptr(o)->add_hard_constraint(to_expr(a));
        Z3_CATCH;
    }

    void Z3_API Z3_optimize_assert_and_track(Z3_context c, Z3_optimize o, Z3_ast a, Z3_ast t) {
        Z3_TRY;
        LOG_Z3_optimize_assert_and_track(c, o, a, t);
        RESET_ERROR_CODE();
        CHECK_FORMULA(a,);        
        CHECK_FORMULA(t,);        
        to_optimize_ptr(o)->add_hard_constraint(to_expr(a), to_expr(t));
        Z3_CATCH;
    }

    unsigned Z3_API Z3_optimize_assert_soft(Z3_context c, Z3_optimize o, Z3_ast a, Z3_string weight, Z3_symbol id) {
        Z3_TRY;
        LOG_Z3_optimize_assert_soft(c, o, a, weight, id);
        RESET_ERROR_CODE();
        CHECK_FORMULA(a,0);        
        rational w(weight);
        return to_optimize_ptr(o)->add_soft_constraint(to_expr(a), w, to_symbol(id));
        Z3_CATCH_RETURN(0);
    }

    unsigned Z3_API Z3_optimize_maximize(Z3_context c, Z3_optimize o, Z3_ast t) {
        Z3_TRY;
        LOG_Z3_optimize_maximize(c, o, t);
        RESET_ERROR_CODE();
        CHECK_VALID_AST(t, 0);        
        CHECK_IS_EXPR(t, 0);
        return to_optimize_ptr(o)->add_objective(to_app(t), true);
        Z3_CATCH_RETURN(0);
    }

    unsigned Z3_API Z3_optimize_minimize(Z3_context c, Z3_optimize o, Z3_ast t) {
        Z3_TRY;
        LOG_Z3_optimize_minimize(c, o, t);
        RESET_ERROR_CODE();
        CHECK_VALID_AST(t, 0);  
        CHECK_IS_EXPR(t, 0);      
        return to_optimize_ptr(o)->add_objective(to_app(t), false);
        Z3_CATCH_RETURN(0);
    }

    void Z3_API Z3_optimize_push(Z3_context c,Z3_optimize d) {
        Z3_TRY;
        LOG_Z3_optimize_push(c, d);
        RESET_ERROR_CODE();
        to_optimize_ptr(d)->push();
        Z3_CATCH;
    }

    void Z3_API Z3_optimize_pop(Z3_context c,Z3_optimize d) {
        Z3_TRY;
        LOG_Z3_optimize_pop(c, d);
        RESET_ERROR_CODE();
        to_optimize_ptr(d)->pop(1);
        Z3_CATCH;
    }


    Z3_lbool Z3_API Z3_optimize_check(Z3_context c, Z3_optimize o, unsigned num_assumptions, Z3_ast const assumptions[]) {
        Z3_TRY;
        LOG_Z3_optimize_check(c, o, num_assumptions, assumptions);
        RESET_ERROR_CODE();
        for (unsigned i = 0; i < num_assumptions; i++) {
            if (!is_expr(to_ast(assumptions[i]))) {
                SET_ERROR_CODE(Z3_INVALID_ARG, "assumption is not an expression");
                return Z3_L_UNDEF;
            }
        }
        lbool r = l_undef;
        cancel_eh<reslimit> eh(mk_c(c)->m().limit());
        unsigned timeout = to_optimize_ptr(o)->get_params().get_uint("timeout", mk_c(c)->get_timeout());
        unsigned rlimit = to_optimize_ptr(o)->get_params().get_uint("rlimit", mk_c(c)->get_rlimit());
        bool     use_ctrl_c  = to_optimize_ptr(o)->get_params().get_bool("ctrl_c", true);
        api::context::set_interruptable si(*(mk_c(c)), eh);        
        {
            scoped_ctrl_c ctrlc(eh, false, use_ctrl_c);
            scoped_timer timer(timeout, &eh);
            scoped_rlimit _rlimit(mk_c(c)->m().limit(), rlimit);
            try {
                expr_ref_vector asms(mk_c(c)->m());
                asms.append(num_assumptions, to_exprs(num_assumptions, assumptions));
                r = to_optimize_ptr(o)->optimize(asms);
            }
            catch (z3_exception& ex) {
                if (mk_c(c)->m().inc()) {
                    mk_c(c)->handle_exception(ex);
                }
                r = l_undef;
                if (!mk_c(c)->m().inc()) {
                    to_optimize_ptr(o)->set_reason_unknown(ex.msg());
                }
                else {
                    mk_c(c)->handle_exception(ex);
                }
            }
            // to_optimize_ref(d).cleanup();
        }
        return of_lbool(r);
        Z3_CATCH_RETURN(Z3_L_UNDEF);
    }

    Z3_ast_vector Z3_API Z3_optimize_get_unsat_core(Z3_context c, Z3_optimize o) {
        Z3_TRY;
        LOG_Z3_optimize_get_unsat_core(c, o);
        RESET_ERROR_CODE();
        expr_ref_vector core(mk_c(c)->m());
        to_optimize_ptr(o)->get_unsat_core(core);
        Z3_ast_vector_ref * v = alloc(Z3_ast_vector_ref, *mk_c(c), mk_c(c)->m());
        mk_c(c)->save_object(v);
        for (expr* e : core) {
            v->m_ast_vector.push_back(e);
        }
        RETURN_Z3(of_ast_vector(v));
        Z3_CATCH_RETURN(nullptr);
    }


    Z3_string Z3_API Z3_optimize_get_reason_unknown(Z3_context c, Z3_optimize o) {
        Z3_TRY;
        LOG_Z3_optimize_get_reason_unknown(c, o);
        RESET_ERROR_CODE();
        return mk_c(c)->mk_external_string(to_optimize_ptr(o)->reason_unknown());
        Z3_CATCH_RETURN("");
    }

    Z3_model Z3_API Z3_optimize_get_model(Z3_context c, Z3_optimize o) {
        Z3_TRY;
        LOG_Z3_optimize_get_model(c, o);
        RESET_ERROR_CODE();
        model_ref _m;
        to_optimize_ptr(o)->get_model(_m);
        Z3_model_ref * m_ref = alloc(Z3_model_ref, *mk_c(c)); 
        if (_m) {
            model_params mp(to_optimize_ptr(o)->get_params());
            if (mp.compact()) _m->compress();
            m_ref->m_model = _m;
        }
        else {
            m_ref->m_model = alloc(model, mk_c(c)->m());
        }
        mk_c(c)->save_object(m_ref);
        RETURN_Z3(of_model(m_ref));
        Z3_CATCH_RETURN(nullptr);
    }

    void Z3_API Z3_optimize_set_params(Z3_context c, Z3_optimize o, Z3_params p) {
        Z3_TRY;
        LOG_Z3_optimize_set_params(c, o, p);
        RESET_ERROR_CODE();
        param_descrs descrs;
        to_optimize_ptr(o)->collect_param_descrs(descrs);
        to_params(p)->m_params.validate(descrs);
        to_optimize_ptr(o)->updt_params(to_param_ref(p));
        Z3_CATCH;
    }
    
    Z3_param_descrs Z3_API Z3_optimize_get_param_descrs(Z3_context c, Z3_optimize o) {
        Z3_TRY;
        LOG_Z3_optimize_get_param_descrs(c, o);
        RESET_ERROR_CODE();
        Z3_param_descrs_ref * d = alloc(Z3_param_descrs_ref, *mk_c(c));
        mk_c(c)->save_object(d);
        to_optimize_ptr(o)->collect_param_descrs(d->m_descrs);
        Z3_param_descrs r = of_param_descrs(d);
        RETURN_Z3(r);
        Z3_CATCH_RETURN(nullptr);
    }
    
    // get lower value or current approximation
    Z3_ast Z3_API Z3_optimize_get_lower(Z3_context c, Z3_optimize o, unsigned idx) {
        Z3_TRY;
        LOG_Z3_optimize_get_lower(c, o, idx);
        RESET_ERROR_CODE();
        expr_ref e = to_optimize_ptr(o)->get_lower(idx);
        mk_c(c)->save_ast_trail(e);
        RETURN_Z3(of_expr(e));
        Z3_CATCH_RETURN(nullptr);
    }

    // get upper or current approximation
    Z3_ast Z3_API Z3_optimize_get_upper(Z3_context c, Z3_optimize o, unsigned idx) {
        Z3_TRY;
        LOG_Z3_optimize_get_upper(c, o, idx);
        RESET_ERROR_CODE();
        expr_ref e = to_optimize_ptr(o)->get_upper(idx);
        mk_c(c)->save_ast_trail(e);
        RETURN_Z3(of_expr(e));
        Z3_CATCH_RETURN(nullptr);
    }

    // get lower value or current approximation
    Z3_ast_vector Z3_API Z3_optimize_get_lower_as_vector(Z3_context c, Z3_optimize o, unsigned idx) {
        Z3_TRY;
        LOG_Z3_optimize_get_lower_as_vector(c, o, idx);
        RESET_ERROR_CODE();
        expr_ref_vector es(mk_c(c)->m());
        to_optimize_ptr(o)->get_lower(idx, es);
        Z3_ast_vector_ref * v = alloc(Z3_ast_vector_ref, *mk_c(c), mk_c(c)->m());
        mk_c(c)->save_object(v);
        v->m_ast_vector.append(es.size(), (ast*const*)es.data());
        RETURN_Z3(of_ast_vector(v));
        Z3_CATCH_RETURN(nullptr);
    }

    // get upper or current approximation
    Z3_ast_vector Z3_API Z3_optimize_get_upper_as_vector(Z3_context c, Z3_optimize o, unsigned idx) {
        Z3_TRY;
        LOG_Z3_optimize_get_upper_as_vector(c, o, idx);
        RESET_ERROR_CODE();
        expr_ref_vector es(mk_c(c)->m());
        to_optimize_ptr(o)->get_upper(idx, es);
        Z3_ast_vector_ref * v = alloc(Z3_ast_vector_ref, *mk_c(c), mk_c(c)->m());
        mk_c(c)->save_object(v);
        v->m_ast_vector.append(es.size(), (ast*const*)es.data());
        RETURN_Z3(of_ast_vector(v));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_string Z3_API Z3_optimize_to_string(Z3_context c, Z3_optimize o) {
        Z3_TRY;
        LOG_Z3_optimize_to_string(c, o);
        RESET_ERROR_CODE();
        return mk_c(c)->mk_external_string(to_optimize_ptr(o)->to_string());
        Z3_CATCH_RETURN("");
    }

    Z3_string Z3_API Z3_optimize_get_help(Z3_context c, Z3_optimize d) {
        Z3_TRY;
        LOG_Z3_optimize_get_help(c, d);
        RESET_ERROR_CODE();
        std::ostringstream buffer;
        param_descrs descrs;
        to_optimize_ptr(d)->collect_param_descrs(descrs);
        descrs.display(buffer);
        return mk_c(c)->mk_external_string(buffer.str());
        Z3_CATCH_RETURN("");
    }

    Z3_stats Z3_API Z3_optimize_get_statistics(Z3_context c,Z3_optimize d) {
        Z3_TRY;
        LOG_Z3_optimize_get_statistics(c, d);
        RESET_ERROR_CODE();
        Z3_stats_ref * st = alloc(Z3_stats_ref, *mk_c(c));
        to_optimize_ptr(d)->collect_statistics(st->m_stats);
        to_optimize_ptr(d)->collect_timer_stats(st->m_stats);
        mk_c(c)->save_object(st);
        Z3_stats r = of_stats(st);
        RETURN_Z3(r);
        Z3_CATCH_RETURN(nullptr);
    }

    static void Z3_optimize_from_stream(
        Z3_context    c,
        Z3_optimize opt,
        std::istream& s, 
        char const* ext) {
        ast_manager& m = mk_c(c)->m();        
        if (ext && std::string("opb") == ext) {
            unsigned_vector h;
            parse_opb(*to_optimize_ptr(opt), s, h);
            return;
        }
        if (ext && std::string("wcnf") == ext) {
            unsigned_vector h;
            parse_wcnf(*to_optimize_ptr(opt), s, h);
            return;
        }
        if (ext && std::string("lp") == ext) {
            unsigned_vector h;
            parse_lp(*to_optimize_ptr(opt), s, h);
            return;
        }
        scoped_ptr<cmd_context> ctx = alloc(cmd_context, false, &m);
        install_opt_cmds(*ctx.get(), to_optimize_ptr(opt));
        std::stringstream errstrm;
        ctx->set_regular_stream(errstrm);
        ctx->set_ignore_check(true);
        try {
            if (!parse_smt2_commands(*ctx.get(), s)) {
                ctx = nullptr;
                SET_ERROR_CODE(Z3_PARSER_ERROR, errstrm.str());
                return;
            }        
        }
        catch (z3_exception& e) {
            errstrm << e.msg();
            ctx = nullptr;
            SET_ERROR_CODE(Z3_PARSER_ERROR, errstrm.str());
            return;
        }

        for (expr * e : ctx->assertions()) {
            to_optimize_ptr(opt)->add_hard_constraint(e);
        }
    }



    void Z3_API Z3_optimize_from_string(
        Z3_context    c,
        Z3_optimize   d,
        Z3_string     s) {
        Z3_TRY;
        //LOG_Z3_optimize_from_string(c, d, s);
        std::string str(s);
        std::istringstream is(str);
        Z3_optimize_from_stream(c, d, is, nullptr);
        Z3_CATCH;
    }

    void Z3_API Z3_optimize_from_file(
        Z3_context    c,
        Z3_optimize   d,
        Z3_string     s) {
        Z3_TRY;
        //LOG_Z3_optimize_from_file(c, d, s);
        std::ifstream is(s);
        if (!is) {
            std::ostringstream strm;
            strm << "Could not open file " << s;
            throw default_exception(strm.str());
        }
        Z3_optimize_from_stream(c, d, is, get_extension(s));
        Z3_CATCH;
    }


    Z3_ast_vector Z3_API Z3_optimize_get_assertions(Z3_context c, Z3_optimize o) {
        Z3_TRY;
        LOG_Z3_optimize_get_assertions(c, o);
        RESET_ERROR_CODE();
        Z3_ast_vector_ref * v = alloc(Z3_ast_vector_ref, *mk_c(c), mk_c(c)->m());
        mk_c(c)->save_object(v);
        expr_ref_vector hard(mk_c(c)->m());
        to_optimize_ptr(o)->get_hard_constraints(hard);
        for (expr* h : hard) {
            v->m_ast_vector.push_back(h);
        }
        RETURN_Z3(of_ast_vector(v));
        Z3_CATCH_RETURN(nullptr);
    }
    
    Z3_ast_vector Z3_API Z3_optimize_get_objectives(Z3_context c, Z3_optimize o) {
        Z3_TRY;
        LOG_Z3_optimize_get_objectives(c, o);
        RESET_ERROR_CODE();
        unsigned n = to_optimize_ptr(o)->num_objectives();
        Z3_ast_vector_ref * v = alloc(Z3_ast_vector_ref, *mk_c(c), mk_c(c)->m());
        mk_c(c)->save_object(v);
        for (unsigned i = 0; i < n; i++) {
            v->m_ast_vector.push_back(to_optimize_ptr(o)->get_objective(i));
        }
        RETURN_Z3(of_ast_vector(v));
        Z3_CATCH_RETURN(nullptr);
    }

    static void optimize_on_model(opt::on_model_t& o, model_ref& m) {
        auto model_eh = (void(*)(void*)) o.on_model;
        Z3_model_ref * m_ref = (Z3_model_ref*) o.m;
        m_ref->m_model = m.get();
        model_eh(o.user_context);
    }

    void Z3_API Z3_optimize_register_model_eh(
        Z3_context   c, 
        Z3_optimize  o, 
        Z3_model     m,
        void*        user_context,
        Z3_model_eh  model_eh) {
        Z3_TRY;

        std::function<void(opt::on_model_t&, model_ref&)> _model_eh = optimize_on_model;
        opt::on_model_t ctx;
        ctx.c = c;
        ctx.m = m;
        ctx.user_context = user_context;
        ctx.on_model = (void*)model_eh;
        to_optimize_ptr(o)->register_on_model(ctx, _model_eh);
        Z3_CATCH;
    }



};
