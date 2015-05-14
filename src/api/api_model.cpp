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
#include<iostream>
#include"z3.h"
#include"api_log_macros.h"
#include"api_context.h"
#include"api_model.h"
#include"api_ast_vector.h"
#include"array_decl_plugin.h"
#include"model.h"
#include"model_v2_pp.h"
#include"model_smt2_pp.h"
#include"model_params.hpp"
#include"model_evaluator_params.hpp"

extern "C" {

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

    Z3_ast Z3_API Z3_model_get_const_interp(Z3_context c, Z3_model m, Z3_func_decl a) {
        Z3_TRY;
        LOG_Z3_model_get_const_interp(c, m, a);
        RESET_ERROR_CODE();
        CHECK_NON_NULL(m, 0);
        expr * r = to_model_ref(m)->get_const_interp(to_func_decl(a));
        if (!r) {
            SET_ERROR_CODE(Z3_INVALID_ARG);
            RETURN_Z3(0);
        }
        mk_c(c)->save_ast_trail(r);
        RETURN_Z3(of_expr(r));
        Z3_CATCH_RETURN(0);
    }

    Z3_bool Z3_API Z3_model_has_interp(Z3_context c, Z3_model m, Z3_func_decl a) {
        Z3_TRY;
        LOG_Z3_model_has_interp(c, m, a);
        CHECK_NON_NULL(m, 0);
        if (to_model_ref(m)->has_interpretation(to_func_decl(a))) {
            return Z3_TRUE;
        } else {
            return Z3_FALSE;
        }
        Z3_CATCH_RETURN(Z3_FALSE);
    }

    Z3_func_interp Z3_API Z3_model_get_func_interp(Z3_context c, Z3_model m, Z3_func_decl f) {
        Z3_TRY;
        LOG_Z3_model_get_func_interp(c, m, f);
        RESET_ERROR_CODE();
        CHECK_NON_NULL(m, 0);
        func_interp * _fi       = to_model_ref(m)->get_func_interp(to_func_decl(f));
        if (!_fi) {
            SET_ERROR_CODE(Z3_INVALID_ARG);
            RETURN_Z3(0);
        }
        Z3_func_interp_ref * fi = alloc(Z3_func_interp_ref, to_model_ref(m));
        fi->m_func_interp       = _fi;
        mk_c(c)->save_object(fi);
        RETURN_Z3(of_func_interp(fi));
        Z3_CATCH_RETURN(0);
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
        CHECK_NON_NULL(m, 0);
        model * _m = to_model_ref(m);
        if (i < _m->get_num_constants()) {
            RETURN_Z3(of_func_decl(_m->get_constant(i))); 
        }
        else {
            SET_ERROR_CODE(Z3_IOB);
            RETURN_Z3(0);
        }
        Z3_CATCH_RETURN(0);
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
        CHECK_NON_NULL(m, 0);
        model * _m = to_model_ref(m);
        if (i >= _m->get_num_functions()) {
            SET_ERROR_CODE(Z3_IOB);
            return 0;
        }
        return of_func_decl(_m->get_function(i));
    }
    
    Z3_func_decl Z3_API Z3_model_get_func_decl(Z3_context c, Z3_model m, unsigned i) {
        Z3_TRY;
        LOG_Z3_get_model_func_decl(c, m, i);
        RESET_ERROR_CODE();
        Z3_func_decl r = get_model_func_decl_core(c, m, i);
        RETURN_Z3(r);
        Z3_CATCH_RETURN(0);
    }
    
    Z3_bool Z3_API Z3_model_eval(Z3_context c, Z3_model m, Z3_ast t, Z3_bool model_completion, Z3_ast * v) {
        Z3_TRY;
        LOG_Z3_model_eval(c, m, t, model_completion, v);
        if (v) *v = 0;
        RESET_ERROR_CODE();
        CHECK_NON_NULL(m, Z3_FALSE);
        model * _m = to_model_ref(m);
        expr_ref result(mk_c(c)->m());
        _m->eval(to_expr(t), result, model_completion == Z3_TRUE);
        mk_c(c)->save_ast_trail(result.get());
        *v = of_ast(result.get());
        RETURN_Z3_model_eval Z3_TRUE;
        Z3_CATCH_RETURN(0);
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
            SET_ERROR_CODE(Z3_IOB);
            RETURN_Z3(0);
        }
        sort * s = to_model_ref(m)->get_uninterpreted_sort(i);
        RETURN_Z3(of_sort(s));
        Z3_CATCH_RETURN(0);
    }

    Z3_ast_vector Z3_API Z3_model_get_sort_universe(Z3_context c, Z3_model m, Z3_sort s) {
        Z3_TRY;
        LOG_Z3_model_get_sort_universe(c, m, s);
        RESET_ERROR_CODE();
        if (!to_model_ref(m)->has_uninterpreted_sort(to_sort(s))) {
            SET_ERROR_CODE(Z3_INVALID_ARG);
            RETURN_Z3(0);
        }
        ptr_vector<expr> const & universe = to_model_ref(m)->get_universe(to_sort(s));
        Z3_ast_vector_ref * v = alloc(Z3_ast_vector_ref, mk_c(c)->m());
        mk_c(c)->save_object(v);
        unsigned sz = universe.size();
        for (unsigned i = 0; i < sz; i++) {
            v->m_ast_vector.push_back(universe[i]);
        }
        RETURN_Z3(of_ast_vector(v));
        Z3_CATCH_RETURN(0);
    }
    
    Z3_bool Z3_API Z3_is_as_array(Z3_context c, Z3_ast a) {
        Z3_TRY;
        LOG_Z3_is_as_array(c, a);
        RESET_ERROR_CODE();
        return is_expr(to_ast(a)) && is_app_of(to_expr(a), mk_c(c)->get_array_fid(), OP_AS_ARRAY);
        Z3_CATCH_RETURN(Z3_FALSE);
    }
    
    Z3_func_decl Z3_API Z3_get_as_array_func_decl(Z3_context c, Z3_ast a) {
        Z3_TRY;
        LOG_Z3_get_as_array_func_decl(c, a);
        RESET_ERROR_CODE();
        if (is_expr(to_ast(a)) && is_app_of(to_expr(a), mk_c(c)->get_array_fid(), OP_AS_ARRAY)) {
            RETURN_Z3(of_func_decl(to_func_decl(to_app(a)->get_decl()->get_parameter(0).get_ast())));
        }
        else {
            SET_ERROR_CODE(Z3_INVALID_ARG);
            RETURN_Z3(0);
        }
        Z3_CATCH_RETURN(0);
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
        CHECK_NON_NULL(f, 0);
        if (i >= to_func_interp_ref(f)->num_entries()) {
            SET_ERROR_CODE(Z3_IOB);
            RETURN_Z3(0);
        }
        Z3_func_entry_ref * e = alloc(Z3_func_entry_ref, to_func_interp(f)->m_model.get());
        e->m_func_interp = to_func_interp_ref(f);
        e->m_func_entry  = to_func_interp_ref(f)->get_entry(i);
        mk_c(c)->save_object(e);
        RETURN_Z3(of_func_entry(e));
        Z3_CATCH_RETURN(0);
    }
    
    Z3_ast Z3_API Z3_func_interp_get_else(Z3_context c, Z3_func_interp f) {
        Z3_TRY;
        LOG_Z3_func_interp_get_else(c, f);
        RESET_ERROR_CODE();
        CHECK_NON_NULL(f, 0);
        expr * e = to_func_interp_ref(f)->get_else();
        mk_c(c)->save_ast_trail(e);
        RETURN_Z3(of_expr(e));
        Z3_CATCH_RETURN(0);
    }

    unsigned Z3_API Z3_func_interp_get_arity(Z3_context c, Z3_func_interp f) {
        Z3_TRY;
        LOG_Z3_func_interp_get_arity(c, f);
        RESET_ERROR_CODE();
        CHECK_NON_NULL(f, 0);
        return to_func_interp_ref(f)->get_arity();
        Z3_CATCH_RETURN(0);
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
        Z3_CATCH_RETURN(0);
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
            SET_ERROR_CODE(Z3_IOB);
            RETURN_Z3(0);
        }
        expr * r = to_func_entry(e)->m_func_entry->get_arg(i);
        RETURN_Z3(of_expr(r));
        Z3_CATCH_RETURN(0);
    }
   
    // ----------------------------
    //
    // DEPRECATED API
    //
    // ----------------------------

    void Z3_API Z3_del_model(Z3_context c, Z3_model  m) {
        Z3_model_dec_ref(c, m);
    }

    unsigned Z3_API Z3_get_model_num_constants(Z3_context c, Z3_model m) {
        return Z3_model_get_num_consts(c, m);
    }

    Z3_func_decl Z3_API Z3_get_model_constant(Z3_context c, Z3_model m, unsigned i) {
        return Z3_model_get_const_decl(c, m, i);
    }

    unsigned Z3_API Z3_get_model_num_funcs(Z3_context c, Z3_model m) {
        return Z3_model_get_num_funcs(c, m);
    }

    Z3_func_decl Z3_API Z3_get_model_func_decl(Z3_context c, Z3_model m, unsigned i) {
        return Z3_model_get_func_decl(c, m, i);
    }
    
    Z3_ast Z3_API Z3_get_model_func_else(Z3_context c, Z3_model m, unsigned i) {
        Z3_TRY;
        LOG_Z3_get_model_func_else(c, m, i);
        RESET_ERROR_CODE();
        CHECK_NON_NULL(m, 0);
        Z3_func_decl d = get_model_func_decl_core(c, m, i);
        if (d) {
            model * _m = to_model_ref(m);            
            func_interp * g = _m->get_func_interp(to_func_decl(d));
            if (g) {
                expr * e = g->get_else();
                mk_c(c)->save_ast_trail(e);
                RETURN_Z3(of_ast(e));
            }
            SET_ERROR_CODE(Z3_IOB);
            RETURN_Z3(0);
        }
        RETURN_Z3(0);
        Z3_CATCH_RETURN(0);
    }

    unsigned get_model_func_num_entries_core(Z3_context c, Z3_model m, unsigned i) {
        RESET_ERROR_CODE();
        CHECK_NON_NULL(m, 0);
        Z3_func_decl d = get_model_func_decl_core(c, m, i);
        if (d) {
            model * _m = to_model_ref(m);            
            func_interp * g = _m->get_func_interp(to_func_decl(d));
            if (g) {
                return g->num_entries();
            }
            SET_ERROR_CODE(Z3_IOB);
            return 0;
        }
        return 0;
    }
    
    unsigned Z3_API Z3_get_model_func_num_entries(Z3_context c, Z3_model m, unsigned i) {
        Z3_TRY;
        LOG_Z3_get_model_func_num_entries(c, m, i);
        return get_model_func_num_entries_core(c, m, i);
        Z3_CATCH_RETURN(0);
    }

    unsigned get_model_func_entry_num_args_core(Z3_context c,
                                                Z3_model m,
                                                unsigned i,
                                                unsigned j) {
        RESET_ERROR_CODE();
        CHECK_NON_NULL(m, 0);
        if (j >= get_model_func_num_entries_core(c, m, i)) {
            SET_ERROR_CODE(Z3_IOB);
            return 0;
        }
        Z3_func_decl d = get_model_func_decl_core(c, m, i);
        if (d) {
            model * _m = to_model_ref(m);
            func_interp * g = _m->get_func_interp(to_func_decl(d));
            return g->get_arity();
        }
        return 0;
    }
    
    unsigned Z3_API Z3_get_model_func_entry_num_args(Z3_context c,
                                                     Z3_model m,
                                                     unsigned i,
                                                     unsigned j) {
        Z3_TRY;
        LOG_Z3_get_model_func_entry_num_args(c, m, i, j);
        return get_model_func_entry_num_args_core(c, m, i, j);
        Z3_CATCH_RETURN(0);
    }

    Z3_ast Z3_API Z3_get_model_func_entry_arg(Z3_context c,
                                                Z3_model m,
                                                unsigned i,
                                                unsigned j,
                                                unsigned k) {
        Z3_TRY;
        LOG_Z3_get_model_func_entry_arg(c, m, i, j, k);
        RESET_ERROR_CODE();
        CHECK_NON_NULL(m, 0);
        if (j >= get_model_func_num_entries_core(c, m, i) || k >= get_model_func_entry_num_args_core(c, m, i, j)) {
            SET_ERROR_CODE(Z3_IOB);
            RETURN_Z3(0);
        }
        Z3_func_decl d = get_model_func_decl_core(c, m, i);
        if (d) {
            model * _m = to_model_ref(m);            
            func_interp * g = _m->get_func_interp(to_func_decl(d));
            if (g && j < g->num_entries()) {
                func_entry const * e = g->get_entry(j);
                if (k < g->get_arity()) {
                    expr * a = e->get_arg(k);
                    mk_c(c)->save_ast_trail(a);
                    RETURN_Z3(of_ast(a));
                }
            }
            SET_ERROR_CODE(Z3_IOB);
            RETURN_Z3(0);
        }
        RETURN_Z3(0);
        Z3_CATCH_RETURN(0);
    }

    Z3_ast Z3_API Z3_get_model_func_entry_value(Z3_context c,
                                                Z3_model m,
                                                unsigned i,
                                                unsigned j) {
        Z3_TRY;
        LOG_Z3_get_model_func_entry_value(c, m, i, j);
        RESET_ERROR_CODE();
        CHECK_NON_NULL(m, 0);
        if (j >= get_model_func_num_entries_core(c, m, i)) {
            SET_ERROR_CODE(Z3_IOB);
            RETURN_Z3(0);
        }
        Z3_func_decl d = get_model_func_decl_core(c, m, i);
        if (d) {
            model * _m = to_model_ref(m);            
            func_interp * g = _m->get_func_interp(to_func_decl(d));
            if (g && j < g->num_entries()) {
                func_entry const* e = g->get_entry(j);
                expr* a = e->get_result();
                mk_c(c)->save_ast_trail(a);
                RETURN_Z3(of_ast(a));
            }
            SET_ERROR_CODE(Z3_IOB);
            RETURN_Z3(0);
        }
        RETURN_Z3(0);
        Z3_CATCH_RETURN(0);
    }
    
    Z3_bool Z3_API Z3_eval(Z3_context c,
                           Z3_model m,
                           Z3_ast t,
                           Z3_ast * v) {
        model_evaluator_params p;
        return Z3_model_eval(c, m, t, p.completion(), v);
    }

    Z3_bool Z3_API Z3_eval_func_decl(Z3_context c, 
                                     Z3_model m, 
                                     Z3_func_decl decl,
                                     Z3_ast* v) {
        Z3_TRY;
        LOG_Z3_eval_func_decl(c, m, decl, v);
        RESET_ERROR_CODE();
        CHECK_NON_NULL(m, Z3_FALSE);
        ast_manager & mgr = mk_c(c)->m();
        model * _m = to_model_ref(m);
        expr_ref result(mgr);
        if( _m->eval(to_func_decl(decl), result)) {
            mk_c(c)->save_ast_trail(result.get());
            *v = of_ast(result.get());
            RETURN_Z3_eval_func_decl Z3_TRUE;
        }
        else {
            return Z3_FALSE;
        }      
        Z3_CATCH_RETURN(Z3_FALSE);
    }


    Z3_bool Z3_API Z3_is_array_value(Z3_context c, Z3_model _m, Z3_ast _v, unsigned* size) {
        Z3_TRY;
        LOG_Z3_is_array_value(c, _m, _v, size);
        RESET_ERROR_CODE();
        CHECK_NON_NULL(_v, Z3_FALSE);
        CHECK_NON_NULL(_m, Z3_FALSE);
        model * m = to_model_ref(_m);
        expr * v = to_expr(_v);
        ast_manager& mgr = mk_c(c)->m();
        family_id afid = mk_c(c)->get_array_fid();
        unsigned sz = 0;
        array_util pl(mgr);
        if (pl.is_as_array(v)) {
            func_decl* f = pl.get_as_array_func_decl(to_app(v));
            func_interp* g = m->get_func_interp(f);
            sz = g->num_entries();
            if (sz > 0 && g->get_arity() != 1) {
                return Z3_FALSE;
            }
        }
        else {
            while (pl.is_store(v)) {
                if (to_app(v)->get_num_args() != 3) {
                    return Z3_FALSE;
                }
                v = to_app(v)->get_arg(0);
                ++sz;
            }
            if (!is_app_of(v, afid, OP_CONST_ARRAY)) {
                return Z3_FALSE;
            }
        }
        if (size) {
            *size = sz;
        }
        return Z3_TRUE;
        Z3_CATCH_RETURN(Z3_FALSE);
    }


    void Z3_API Z3_get_array_value(Z3_context c, 
                                   Z3_model _m,
                                   Z3_ast _v,
                                   unsigned num_entries,
                                   Z3_ast indices[],
                                   Z3_ast values[],
                                   Z3_ast* else_value) {
        Z3_TRY;
        LOG_Z3_get_array_value(c, _m, _v, num_entries, indices, values, else_value);
        RESET_ERROR_CODE();
        CHECK_NON_NULL(_m, );
        model * m = to_model_ref(_m);

        expr* v = to_expr(_v);
        family_id afid = mk_c(c)->get_array_fid();
        ast_manager& mgr = mk_c(c)->m();
        array_util pl(mgr);

        //
        // note: _v is already reference counted.
        // saving the trail for the returned values 
        // is redundant.
        //
        unsigned sz = 0;
        if (pl.is_as_array(v)) {
            func_decl* f = pl.get_as_array_func_decl(to_app(v));
            func_interp* g = m->get_func_interp(f);
            sz = g->num_entries();
            if (g->get_arity() != 1) {
                SET_ERROR_CODE(Z3_INVALID_ARG);
                return;
            }
            for (unsigned i = 0; i < sz && i < num_entries; ++i) {
                indices[i] = of_ast(g->get_entry(i)->get_arg(0));
                values[i] = of_ast(g->get_entry(i)->get_result());                
            }
            if (else_value) {
                *else_value = of_ast(g->get_else());
            }                       
        }
        else {
            while (sz <= num_entries && is_app_of(v, afid, OP_STORE)) {
                app* a = to_app(v);
                if (a->get_num_args() != 3) {
                    SET_ERROR_CODE(Z3_INVALID_ARG);
                    return;
                }
                expr* idx = a->get_arg(1);
                expr* val = a->get_arg(2);
                indices[sz] = of_ast(idx);
                values[sz] = of_ast(val);
                v = to_app(v)->get_arg(0);   
                ++sz;
            }
        
            if (is_app_of(v, afid, OP_CONST_ARRAY)) {
                if (else_value) {
                    *else_value = of_ast(to_app(v)->get_arg(0));
                }
            }
            else {
                SET_ERROR_CODE(Z3_INVALID_ARG);
                return;
            }
        }
        RETURN_Z3_get_array_value;
        Z3_CATCH;
    }

    Z3_bool Z3_API Z3_eval_decl(Z3_context c, 
                                Z3_model m, 
                                Z3_func_decl d, 
                                unsigned num_args,
                                Z3_ast const args[],
                                Z3_ast* v) {
        Z3_TRY;
        LOG_Z3_eval_decl(c, m, d, num_args, args, v);
        RESET_ERROR_CODE();
        CHECK_NON_NULL(m, Z3_FALSE);
        ast_manager & mgr = mk_c(c)->m();
        model * _m = to_model_ref(m);
        app_ref app(mgr);
        app = mgr.mk_app(to_func_decl(d), num_args, to_exprs(args));
        expr_ref result(mgr);
        _m->eval(app.get(), result);
        mk_c(c)->save_ast_trail(result.get());
        *v = of_ast(result.get());
        RETURN_Z3_eval_decl Z3_TRUE;
        Z3_CATCH_RETURN(Z3_FALSE);
    }

    Z3_API char const * Z3_model_to_string(Z3_context c, Z3_model m) {
        Z3_TRY;
        LOG_Z3_model_to_string(c, m);
        RESET_ERROR_CODE();
        CHECK_NON_NULL(m, 0);
        std::ostringstream buffer;
        std::string result;
        if (mk_c(c)->get_print_mode() == Z3_PRINT_SMTLIB2_COMPLIANT) {
            model_smt2_pp(buffer, mk_c(c)->m(), *(to_model_ref(m)), 0);
            // Hack for removing the trailing '\n'
            result = buffer.str();
            if (result.size() != 0)
                result.resize(result.size()-1);
        }
        else {
            model_params p;
            model_v2_pp(buffer, *(to_model_ref(m)), p.partial());
            result = buffer.str();
        }
        return mk_c(c)->mk_external_string(result);
        Z3_CATCH_RETURN(0);
    }

};
