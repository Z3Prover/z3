/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    api_quant.cpp

Abstract:
    API for models

Author:

    Leonardo de Moura (leonardo) 2012-02-29.

Revision History:

--*/
#include "api/z3.h"
#include "api/api_log_macros.h"
#include "api/api_context.h"
#include "api/api_model.h"
#include "api/api_ast_vector.h"
#include "ast/array_decl_plugin.h"
#include "model/model.h"
#include "model/model_v2_pp.h"
#include "model/model_smt2_pp.h"
#include "model/model_params.hpp"
#include "model/model_evaluator_params.hpp"

extern "C" {

    Z3_model Z3_API Z3_mk_model(Z3_context c) {
        Z3_TRY;
        LOG_Z3_mk_model(c);
        RESET_ERROR_CODE();
        Z3_model_ref * m_ref = alloc(Z3_model_ref, *mk_c(c)); 
        m_ref->m_model = alloc(model, mk_c(c)->m());
        mk_c(c)->save_object(m_ref);
        RETURN_Z3(of_model(m_ref));
        Z3_CATCH_RETURN(nullptr);
    }

    void Z3_API Z3_model_inc_ref(Z3_context c, Z3_model m) {
        Z3_TRY;
        LOG_Z3_model_inc_ref(c, m);
        RESET_ERROR_CODE();
        if (m) {
            to_model(m)->inc_ref();
        }
        Z3_CATCH;
    }

    void Z3_API Z3_model_dec_ref(Z3_context c, Z3_model m) {
        Z3_TRY;
        LOG_Z3_model_dec_ref(c, m);
        RESET_ERROR_CODE();
        if (m) {
            to_model(m)->dec_ref();
        }
        Z3_CATCH;
    }

    Z3_ast_opt Z3_API Z3_model_get_const_interp(Z3_context c, Z3_model m, Z3_func_decl a) {
        Z3_TRY;
        LOG_Z3_model_get_const_interp(c, m, a);
        RESET_ERROR_CODE();
        CHECK_NON_NULL(m, nullptr);
        expr * r = to_model_ref(m)->get_const_interp(to_func_decl(a));
        if (!r) {
            RETURN_Z3(nullptr);
        }
        mk_c(c)->save_ast_trail(r);
        RETURN_Z3(of_expr(r));
        Z3_CATCH_RETURN(nullptr);
    }

    bool Z3_API Z3_model_has_interp(Z3_context c, Z3_model m, Z3_func_decl a) {
        Z3_TRY;
        LOG_Z3_model_has_interp(c, m, a);
        CHECK_NON_NULL(m, 0);
        return to_model_ref(m)->has_interpretation(to_func_decl(a));
        Z3_CATCH_RETURN(false);
    }

    Z3_func_interp Z3_API Z3_model_get_func_interp(Z3_context c, Z3_model m, Z3_func_decl f) {
        Z3_TRY;
        LOG_Z3_model_get_func_interp(c, m, f);
        RESET_ERROR_CODE();
        CHECK_NON_NULL(m, nullptr);
        func_interp * _fi       = to_model_ref(m)->get_func_interp(to_func_decl(f));
        if (!_fi) {
            RETURN_Z3(nullptr);
        }
        Z3_func_interp_ref * fi = alloc(Z3_func_interp_ref, *mk_c(c), to_model_ref(m));
        fi->m_func_interp       = _fi;
        mk_c(c)->save_object(fi);
        RETURN_Z3(of_func_interp(fi));
        Z3_CATCH_RETURN(nullptr);
    }

    unsigned Z3_API Z3_model_get_num_consts(Z3_context c, Z3_model m) {
        Z3_TRY;
        LOG_Z3_model_get_num_consts(c, m);
        RESET_ERROR_CODE();
        CHECK_NON_NULL(m, 0);
        return to_model_ref(m)->get_num_constants();
        Z3_CATCH_RETURN(0);
    }

    Z3_func_decl Z3_API Z3_model_get_const_decl(Z3_context c, Z3_model m, unsigned i) {
        Z3_TRY;
        LOG_Z3_model_get_const_decl(c, m, i);
        RESET_ERROR_CODE();
        CHECK_NON_NULL(m, nullptr);
        model * _m = to_model_ref(m);
        if (i < _m->get_num_constants()) {
            RETURN_Z3(of_func_decl(_m->get_constant(i))); 
        }
        else {
            SET_ERROR_CODE(Z3_IOB, nullptr);
            RETURN_Z3(nullptr);
        }
        Z3_CATCH_RETURN(nullptr);
    }
    
    unsigned Z3_API Z3_model_get_num_funcs(Z3_context c, Z3_model m) {
        Z3_TRY;
        LOG_Z3_model_get_num_funcs(c, m);
        RESET_ERROR_CODE();
        CHECK_NON_NULL(m, 0);
        return to_model_ref(m)->get_num_functions();
        Z3_CATCH_RETURN(0);
    }

    Z3_func_decl get_model_func_decl_core(Z3_context c, Z3_model m, unsigned i) {
        CHECK_NON_NULL(m, nullptr);
        model * _m = to_model_ref(m);
        if (i >= _m->get_num_functions()) {
            SET_ERROR_CODE(Z3_IOB, nullptr);
            return nullptr;
        }
        return of_func_decl(_m->get_function(i));
    }
    
    Z3_func_decl Z3_API Z3_model_get_func_decl(Z3_context c, Z3_model m, unsigned i) {
        Z3_TRY;
        LOG_Z3_model_get_func_decl(c, m, i);
        RESET_ERROR_CODE();
        Z3_func_decl r = get_model_func_decl_core(c, m, i);
        RETURN_Z3(r);
        Z3_CATCH_RETURN(nullptr);
    }
    
    bool Z3_API Z3_model_eval(Z3_context c, Z3_model m, Z3_ast t, bool model_completion, Z3_ast * v) {
        Z3_TRY;
        LOG_Z3_model_eval(c, m, t, model_completion, v);
        if (v) *v = nullptr;
        RESET_ERROR_CODE();
        CHECK_NON_NULL(m, false);
        CHECK_IS_EXPR(t, false);
        model * _m = to_model_ref(m);
        params_ref p;
        ast_manager& mgr = mk_c(c)->m();
        if (!_m->has_solver()) {
            _m->set_solver(alloc(api::seq_expr_solver, mgr, p));
        }
        expr_ref result(mgr);
        model::scoped_model_completion _scm(*_m, model_completion);
        result = (*_m)(to_expr(t));
        mk_c(c)->save_ast_trail(result.get());
        *v = of_ast(result.get());
        RETURN_Z3_model_eval true;
        Z3_CATCH_RETURN(false);
    }

    unsigned Z3_API Z3_model_get_num_sorts(Z3_context c, Z3_model m) {
        Z3_TRY;
        LOG_Z3_model_get_num_sorts(c, m);
        RESET_ERROR_CODE();
        return to_model_ref(m)->get_num_uninterpreted_sorts();
        Z3_CATCH_RETURN(0);
    }

    Z3_sort Z3_API Z3_model_get_sort(Z3_context c, Z3_model m, unsigned i) {
        Z3_TRY;
        LOG_Z3_model_get_sort(c, m, i);
        RESET_ERROR_CODE();
        if (i >= to_model_ref(m)->get_num_uninterpreted_sorts()) {
            SET_ERROR_CODE(Z3_IOB, nullptr);
            RETURN_Z3(nullptr);
        }
        sort * s = to_model_ref(m)->get_uninterpreted_sort(i);
        RETURN_Z3(of_sort(s));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast_vector Z3_API Z3_model_get_sort_universe(Z3_context c, Z3_model m, Z3_sort s) {
        Z3_TRY;
        LOG_Z3_model_get_sort_universe(c, m, s);
        RESET_ERROR_CODE();
        if (!to_model_ref(m)->has_uninterpreted_sort(to_sort(s))) {
            SET_ERROR_CODE(Z3_INVALID_ARG, nullptr);
            RETURN_Z3(nullptr);
        }
        ptr_vector<expr> const & universe = to_model_ref(m)->get_universe(to_sort(s));
        Z3_ast_vector_ref * v = alloc(Z3_ast_vector_ref, *mk_c(c), mk_c(c)->m());
        mk_c(c)->save_object(v);
        for (expr * e : universe) {
            v->m_ast_vector.push_back(e);
        }
        RETURN_Z3(of_ast_vector(v));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_model Z3_API Z3_model_translate(Z3_context c, Z3_model m, Z3_context target) {
        Z3_TRY;
        LOG_Z3_model_translate(c, m, target);
        RESET_ERROR_CODE();
        Z3_model_ref* dst = alloc(Z3_model_ref, *mk_c(target));
        ast_translation tr(mk_c(c)->m(), mk_c(target)->m());
        dst->m_model = to_model_ref(m)->translate(tr);
        mk_c(target)->save_object(dst);
        RETURN_Z3(of_model(dst));
        Z3_CATCH_RETURN(nullptr);
    }
    
    bool Z3_API Z3_is_as_array(Z3_context c, Z3_ast a) {
        Z3_TRY;
        LOG_Z3_is_as_array(c, a);
        RESET_ERROR_CODE();
        return a && is_expr(to_ast(a)) && is_app_of(to_expr(a), mk_c(c)->get_array_fid(), OP_AS_ARRAY);
        Z3_CATCH_RETURN(false);
    }
    
    Z3_func_decl Z3_API Z3_get_as_array_func_decl(Z3_context c, Z3_ast a) {
        Z3_TRY;
        LOG_Z3_get_as_array_func_decl(c, a);
        RESET_ERROR_CODE();
        if (a && is_expr(to_ast(a)) && is_app_of(to_expr(a), mk_c(c)->get_array_fid(), OP_AS_ARRAY)) {
            RETURN_Z3(of_func_decl(to_func_decl(to_app(a)->get_decl()->get_parameter(0).get_ast())));
        }
        else {
            SET_ERROR_CODE(Z3_INVALID_ARG, nullptr);
            RETURN_Z3(nullptr);
        }
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_func_interp Z3_API Z3_add_func_interp(Z3_context c, Z3_model m, Z3_func_decl f, Z3_ast else_val) {
        Z3_TRY;
        LOG_Z3_add_func_interp(c, m, f, else_val);
        RESET_ERROR_CODE();
		CHECK_NON_NULL(f, nullptr);
        func_decl* d = to_func_decl(f);
        model* mdl = to_model_ref(m);
        Z3_func_interp_ref * f_ref = alloc(Z3_func_interp_ref, *mk_c(c), mdl); 
        f_ref->m_func_interp = alloc(func_interp, mk_c(c)->m(), d->get_arity());
        mk_c(c)->save_object(f_ref);
        mdl->register_decl(d, f_ref->m_func_interp);
        f_ref->m_func_interp->set_else(to_expr(else_val));
        RETURN_Z3(of_func_interp(f_ref));
        Z3_CATCH_RETURN(nullptr);
    }

    void Z3_API Z3_add_const_interp(Z3_context c, Z3_model m, Z3_func_decl f, Z3_ast a) {
        Z3_TRY;
        LOG_Z3_add_const_interp(c, m, f, a);
        RESET_ERROR_CODE();
        func_decl* d = to_func_decl(f);
        if (!d || d->get_arity() != 0) {
            SET_ERROR_CODE(Z3_INVALID_ARG, nullptr);
        }
        else {
            model* mdl = to_model_ref(m);
            mdl->register_decl(d, to_expr(a));
        }
        Z3_CATCH;
    }

    void Z3_API Z3_func_interp_inc_ref(Z3_context c, Z3_func_interp f) {
        Z3_TRY;
        LOG_Z3_func_interp_inc_ref(c, f);
        RESET_ERROR_CODE();
        if (f) {
            to_func_interp(f)->inc_ref();
        }
        Z3_CATCH;
    }

    void Z3_API Z3_func_interp_dec_ref(Z3_context c, Z3_func_interp f) {
        Z3_TRY;
        LOG_Z3_func_interp_dec_ref(c, f);
        RESET_ERROR_CODE();
        if (f) {
            to_func_interp(f)->dec_ref();
        }
        Z3_CATCH;
    }
    
    unsigned Z3_API Z3_func_interp_get_num_entries(Z3_context c, Z3_func_interp f) {
        Z3_TRY;
        LOG_Z3_func_interp_get_num_entries(c, f);
        RESET_ERROR_CODE();
        CHECK_NON_NULL(f, 0);
        return to_func_interp_ref(f)->num_entries();
        Z3_CATCH_RETURN(0);
    }

    Z3_func_entry Z3_API Z3_func_interp_get_entry(Z3_context c, Z3_func_interp f, unsigned i) {
        Z3_TRY;
        LOG_Z3_func_interp_get_entry(c, f, i);
        RESET_ERROR_CODE();
        CHECK_NON_NULL(f, nullptr);
        if (i >= to_func_interp_ref(f)->num_entries()) {
            SET_ERROR_CODE(Z3_IOB, nullptr);
            RETURN_Z3(nullptr);
        }
        Z3_func_entry_ref * e = alloc(Z3_func_entry_ref, *mk_c(c), to_func_interp(f)->m_model.get());
        e->m_func_interp = to_func_interp_ref(f);
        e->m_func_entry  = to_func_interp_ref(f)->get_entry(i);
        mk_c(c)->save_object(e);
        RETURN_Z3(of_func_entry(e));
        Z3_CATCH_RETURN(nullptr);
    }
    
    Z3_ast Z3_API Z3_func_interp_get_else(Z3_context c, Z3_func_interp f) {
        Z3_TRY;
        LOG_Z3_func_interp_get_else(c, f);
        RESET_ERROR_CODE();
        CHECK_NON_NULL(f, nullptr);
        expr * e = to_func_interp_ref(f)->get_else();
        if (e) {
            mk_c(c)->save_ast_trail(e);
        }
        RETURN_Z3(of_expr(e));
        Z3_CATCH_RETURN(nullptr);
    }

    void Z3_API Z3_func_interp_set_else(Z3_context c, Z3_func_interp f, Z3_ast else_value) {
        Z3_TRY;
        LOG_Z3_func_interp_set_else(c, f, else_value);
        RESET_ERROR_CODE();
        // CHECK_NON_NULL(f, 0);
        to_func_interp_ref(f)->set_else(to_expr(else_value));
        Z3_CATCH;
    }

    unsigned Z3_API Z3_func_interp_get_arity(Z3_context c, Z3_func_interp f) {
        Z3_TRY;
        LOG_Z3_func_interp_get_arity(c, f);
        RESET_ERROR_CODE();
        CHECK_NON_NULL(f, 0);
        return to_func_interp_ref(f)->get_arity();
        Z3_CATCH_RETURN(0);
    }

    void Z3_API Z3_func_interp_add_entry(Z3_context c, Z3_func_interp fi, Z3_ast_vector args, Z3_ast value) {
        Z3_TRY;
        LOG_Z3_func_interp_add_entry(c, fi, args, value);
        //CHECK_NON_NULL(fi, void);
        //CHECK_NON_NULL(args, void);
        //CHECK_NON_NULL(value, void);
        func_interp* _fi = to_func_interp_ref(fi);
        expr* _value = to_expr(value);
        if (to_ast_vector_ref(args).size() != _fi->get_arity()) {
            SET_ERROR_CODE(Z3_IOB, nullptr);
            return;
        }
        // check sorts of value
        expr* const* _args = (expr* const*) to_ast_vector_ref(args).data();
        _fi->insert_entry(_args, _value);
        Z3_CATCH;
    }

    void Z3_API Z3_func_entry_inc_ref(Z3_context c, Z3_func_entry e) {
        Z3_TRY;
        LOG_Z3_func_entry_inc_ref(c, e);
        RESET_ERROR_CODE();
        if (e) {
            to_func_entry(e)->inc_ref();
        }
        Z3_CATCH;
    }

    void Z3_API Z3_func_entry_dec_ref(Z3_context c, Z3_func_entry e) {
        Z3_TRY;
        LOG_Z3_func_entry_dec_ref(c, e);
        RESET_ERROR_CODE();
        if (e) {
            to_func_entry(e)->dec_ref();
        }
        Z3_CATCH;
    }
    
    Z3_ast Z3_API Z3_func_entry_get_value(Z3_context c, Z3_func_entry e) {
        Z3_TRY;
        LOG_Z3_func_entry_get_value(c, e);
        RESET_ERROR_CODE();
        expr * v = to_func_entry_ref(e)->get_result();
        mk_c(c)->save_ast_trail(v);
        RETURN_Z3(of_expr(v));
        Z3_CATCH_RETURN(nullptr);
    }

    unsigned Z3_API Z3_func_entry_get_num_args(Z3_context c, Z3_func_entry e) {
        Z3_TRY;
        LOG_Z3_func_entry_get_num_args(c, e);
        RESET_ERROR_CODE();
        return to_func_entry(e)->m_func_interp->get_arity();
        Z3_CATCH_RETURN(0);
    }
    
    Z3_ast Z3_API Z3_func_entry_get_arg(Z3_context c, Z3_func_entry e, unsigned i) {
        Z3_TRY;
        LOG_Z3_func_entry_get_arg(c, e, i);
        RESET_ERROR_CODE();
        if (i >= to_func_entry(e)->m_func_interp->get_arity()) {
            SET_ERROR_CODE(Z3_IOB, nullptr);
            RETURN_Z3(nullptr);
        }
        expr * r = to_func_entry(e)->m_func_entry->get_arg(i);
        RETURN_Z3(of_expr(r));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_API char const * Z3_model_to_string(Z3_context c, Z3_model m) {
        Z3_TRY;
        LOG_Z3_model_to_string(c, m);
        RESET_ERROR_CODE();
        CHECK_NON_NULL(m, nullptr);
        std::ostringstream buffer;
        std::string result;
        if (mk_c(c)->get_print_mode() == Z3_PRINT_SMTLIB2_COMPLIANT) {
            model_smt2_pp(buffer, mk_c(c)->m(), *(to_model_ref(m)), 0);
            // Hack for removing the trailing '\n'
            result = buffer.str();
            if (!result.empty())
                result.resize(result.size()-1);
        }
        else {
            model_params p;
            model_v2_pp(buffer, *(to_model_ref(m)), p.partial());
            result = buffer.str();
        }
        return mk_c(c)->mk_external_string(std::move(result));
        Z3_CATCH_RETURN(nullptr);
    }

};
