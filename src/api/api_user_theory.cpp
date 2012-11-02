/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    api_user_theory.cpp

Abstract:
    API for external theories

Author:

    Leonardo de Moura (leonardo) 2012-02-29.

Revision History:

--*/
#include<iostream>
#include"z3.h"
#include"api_log_macros.h"
#include"api_context.h"
#include"api_util.h"
#include"user_smt_theory.h"

smt::user_theory * mk_t(Z3_theory t) {
    return reinterpret_cast<smt::user_theory*>(t);
}

extern "C" {

    ///////////////////////////////
    // Theory plugin
    // No support for logging

    Z3_theory Z3_mk_theory(Z3_context c, Z3_string th_name, void * ext_data) {
        Z3_TRY;
        RESET_ERROR_CODE();
        if (mk_c(c)->get_smt_kernel().get_scope_level() > 0) {
            SET_ERROR_CODE(Z3_INVALID_USAGE);
            return 0;
        }
        return reinterpret_cast<Z3_theory>(mk_user_theory(mk_c(c)->get_smt_kernel(), c, ext_data, th_name));
        Z3_CATCH_RETURN(0);
    }

    void * Z3_theory_get_ext_data(Z3_theory t) {
        Z3_context c = Z3_theory_get_context(t);
        Z3_TRY;
        RESET_ERROR_CODE();
        void * r = mk_t(t)->get_ext_data();
        return r;
        Z3_CATCH_RETURN(0);
    }
    
    Z3_sort Z3_theory_mk_sort(Z3_context c, Z3_theory t, Z3_symbol s) {
        Z3_TRY;
        RESET_ERROR_CODE();
        sort * r = mk_t(t)->mk_sort(to_symbol(s));
        mk_c(c)->save_ast_trail(r);
        return of_sort(r);
        Z3_CATCH_RETURN(0);
    }
    
    Z3_ast Z3_theory_mk_value(Z3_context c, Z3_theory t, Z3_symbol n, Z3_sort s) {
        Z3_TRY;
        RESET_ERROR_CODE();
        func_decl * d = mk_t(t)->mk_value_decl(to_symbol(n), to_sort(s));
        app * r       = mk_c(c)->m().mk_const(d);
        mk_c(c)->save_ast_trail(r);
        return of_ast(r);
        Z3_CATCH_RETURN(0);
    }
    
    Z3_ast Z3_theory_mk_constant(Z3_context c, Z3_theory t, Z3_symbol n, Z3_sort s) {
        Z3_TRY;
        RESET_ERROR_CODE();
        Z3_func_decl d = Z3_theory_mk_func_decl(c, t, n, 0, 0, s);
        app * r        = mk_c(c)->m().mk_const(to_func_decl(d));
        mk_c(c)->save_ast_trail(r);
        return of_ast(r);
        Z3_CATCH_RETURN(0);
    }
    
    Z3_func_decl Z3_theory_mk_func_decl(Z3_context c, Z3_theory t, Z3_symbol n,
                                        unsigned domain_size, Z3_sort const domain[],
                                        Z3_sort range) {
        Z3_TRY;
        RESET_ERROR_CODE();
        func_decl * r = mk_t(t)->mk_func_decl(to_symbol(n), domain_size, to_sorts(domain), to_sort(range));
        mk_c(c)->save_ast_trail(r);
        return of_func_decl(r);
        Z3_CATCH_RETURN(0);
    }

    Z3_context Z3_theory_get_context(Z3_theory t) {
        Z3_context c = reinterpret_cast<Z3_context>(mk_t(t)->get_ext_context());
        RESET_ERROR_CODE();
        return c;
    }

    void Z3_set_delete_callback(Z3_theory t, Z3_theory_callback_fptr f) {
        Z3_context c = Z3_theory_get_context(t);
        Z3_TRY;
        RESET_ERROR_CODE();
        mk_t(t)->set_delete_fptr(reinterpret_cast<smt::theory_callback_fptr>(f));
        Z3_CATCH;
    }

    void Z3_set_reduce_app_callback(Z3_theory t, Z3_reduce_app_callback_fptr f) {
        Z3_context c = Z3_theory_get_context(t);
        Z3_TRY;
        RESET_ERROR_CODE();
        mk_t(t)->set_reduce_app_fptr(reinterpret_cast<reduce_app_fptr>(f));
        Z3_CATCH;
    }

    void Z3_set_reduce_eq_callback(Z3_theory t, Z3_reduce_eq_callback_fptr f) {
        Z3_context c = Z3_theory_get_context(t);
        Z3_TRY;
        RESET_ERROR_CODE();
        mk_t(t)->set_reduce_eq_fptr(reinterpret_cast<reduce_eq_fptr>(f));
        Z3_CATCH;
    }

    void Z3_set_reduce_distinct_callback(Z3_theory t, Z3_reduce_distinct_callback_fptr f) {
        Z3_context c = Z3_theory_get_context(t); 
        Z3_TRY;
        RESET_ERROR_CODE();
        mk_t(t)->set_reduce_distinct_fptr(reinterpret_cast<reduce_distinct_fptr>(f));
        Z3_CATCH;
    }

    void Z3_set_new_app_callback(Z3_theory t, Z3_theory_ast_callback_fptr f) {
        Z3_context c = Z3_theory_get_context(t);
        Z3_TRY; 
        RESET_ERROR_CODE();
        mk_t(t)->set_new_app_fptr(reinterpret_cast<smt::theory_app_callback_fptr>(f));
        Z3_CATCH;
    }

    void Z3_set_new_elem_callback(Z3_theory t, Z3_theory_ast_callback_fptr f) {
        Z3_context c = Z3_theory_get_context(t);
        Z3_TRY;
        RESET_ERROR_CODE();
        mk_t(t)->set_new_elem_fptr(reinterpret_cast<smt::theory_app_callback_fptr>(f));
        Z3_CATCH;
    }

    void Z3_set_init_search_callback(Z3_theory t, Z3_theory_callback_fptr f) {
        Z3_context c = Z3_theory_get_context(t);
        Z3_TRY;
        RESET_ERROR_CODE();
        mk_t(t)->set_init_search_fptr(reinterpret_cast<smt::theory_callback_fptr>(f));
        Z3_CATCH;
    }
        
    void Z3_set_push_callback(Z3_theory t, Z3_theory_callback_fptr f) {
        Z3_context c = Z3_theory_get_context(t);
        Z3_TRY;
        RESET_ERROR_CODE();
        mk_t(t)->set_push_fptr(reinterpret_cast<smt::theory_callback_fptr>(f));
        Z3_CATCH;
    }
 
    void Z3_set_pop_callback(Z3_theory t, Z3_theory_callback_fptr f) {
        Z3_context c = Z3_theory_get_context(t);
        Z3_TRY;
        RESET_ERROR_CODE();
        mk_t(t)->set_pop_fptr(reinterpret_cast<smt::theory_callback_fptr>(f));
        Z3_CATCH;
    }

    void Z3_set_restart_callback(Z3_theory t, Z3_theory_callback_fptr f) {
        Z3_context c = Z3_theory_get_context(t);
        Z3_TRY;
        RESET_ERROR_CODE();
        mk_t(t)->set_restart_fptr(reinterpret_cast<smt::theory_callback_fptr>(f));
        Z3_CATCH;
    }

    void Z3_set_reset_callback(Z3_theory t, Z3_theory_callback_fptr f) {
        Z3_context c = Z3_theory_get_context(t);
        Z3_TRY;
        RESET_ERROR_CODE();
        mk_t(t)->set_reset_fptr(reinterpret_cast<smt::theory_callback_fptr>(f));
        Z3_CATCH;
    }
    
    void Z3_set_final_check_callback(Z3_theory t, Z3_theory_final_check_callback_fptr f) {
        Z3_context c = Z3_theory_get_context(t);
        Z3_TRY;
        RESET_ERROR_CODE();
        mk_t(t)->set_final_check_fptr(reinterpret_cast<smt::theory_final_check_callback_fptr>(f));
        Z3_CATCH;
    }
        
    void Z3_set_new_eq_callback(Z3_theory t, Z3_theory_ast_ast_callback_fptr f) {
        Z3_context c = Z3_theory_get_context(t);
        Z3_TRY;
        RESET_ERROR_CODE();
        mk_t(t)->set_new_eq_fptr(reinterpret_cast<smt::theory_app_app_callback_fptr>(f));
        Z3_CATCH;
    }

    void Z3_set_new_diseq_callback(Z3_theory t, Z3_theory_ast_ast_callback_fptr f) {
        Z3_context c = Z3_theory_get_context(t);
        Z3_TRY;
        RESET_ERROR_CODE();
        mk_t(t)->set_new_diseq_fptr(reinterpret_cast<smt::theory_app_app_callback_fptr>(f));
        Z3_CATCH;
    }
    
    void Z3_set_new_assignment_callback(Z3_theory t, Z3_theory_ast_bool_callback_fptr f) {
        Z3_context c = Z3_theory_get_context(t);
        Z3_TRY;
        RESET_ERROR_CODE();
        mk_t(t)->set_new_assignment_fptr(reinterpret_cast<smt::theory_app_bool_callback_fptr>(f));
        Z3_CATCH;
    }

    void Z3_set_new_relevant_callback(Z3_theory t, Z3_theory_ast_callback_fptr f) {
        Z3_context c = Z3_theory_get_context(t);
        Z3_TRY;
        RESET_ERROR_CODE();
        mk_t(t)->set_new_relevant_fptr(reinterpret_cast<smt::theory_app_callback_fptr>(f));
        Z3_CATCH;
    }
    
    void Z3_theory_assert_axiom(Z3_theory t, Z3_ast ax) {
        Z3_context c = Z3_theory_get_context(t);
        Z3_TRY;
        RESET_ERROR_CODE();
        mk_t(t)->assert_axiom(to_ast(ax));
        Z3_CATCH;
    }

    void Z3_theory_assume_eq(Z3_theory t, Z3_ast lhs, Z3_ast rhs) {
        Z3_context c = Z3_theory_get_context(t);
        Z3_TRY;
        RESET_ERROR_CODE();
        mk_t(t)->assume_eq(to_ast(lhs), to_ast(rhs));
        Z3_CATCH;
    }

    void Z3_theory_enable_axiom_simplification(Z3_theory t, Z3_bool flag) {
        Z3_context c = Z3_theory_get_context(t);
        Z3_TRY; 
        RESET_ERROR_CODE();
        mk_t(t)->enable_axiom_simplification(flag == Z3_TRUE);
        Z3_CATCH;
    }

    Z3_ast Z3_theory_get_eqc_root(Z3_theory t, Z3_ast n) {
        Z3_context c = Z3_theory_get_context(t);
        Z3_TRY;
        RESET_ERROR_CODE();
        return of_ast(mk_t(t)->get_root(to_ast(n)));
        Z3_CATCH_RETURN(0);
    }

    Z3_ast Z3_theory_get_eqc_next(Z3_theory t, Z3_ast n) {
        Z3_context c = Z3_theory_get_context(t);
        Z3_TRY;
        RESET_ERROR_CODE();
        return of_ast(mk_t(t)->get_next(to_ast(n)));
        Z3_CATCH_RETURN(0);
    }

    unsigned Z3_theory_get_num_parents(Z3_theory t, Z3_ast n) {
        Z3_context c = Z3_theory_get_context(t);
        Z3_TRY;
        RESET_ERROR_CODE();
        return mk_t(t)->get_num_parents(to_ast(n));
        Z3_CATCH_RETURN(0);
    }
    
    Z3_ast Z3_theory_get_parent(Z3_theory t, Z3_ast n, unsigned i) {
        Z3_context c = Z3_theory_get_context(t);
        Z3_TRY;
        RESET_ERROR_CODE();
        return of_ast(mk_t(t)->get_parent(to_ast(n), i));
        Z3_CATCH_RETURN(0);
    }

    unsigned Z3_theory_get_num_elems(Z3_theory t) {
        Z3_context c = Z3_theory_get_context(t);
        Z3_TRY;
        RESET_ERROR_CODE();
        return mk_t(t)->get_num_asts();
        Z3_CATCH_RETURN(0);
    }

    Z3_ast Z3_theory_get_elem(Z3_theory t, unsigned i) {
        Z3_context c = Z3_theory_get_context(t);
        Z3_TRY;
        RESET_ERROR_CODE();
        return of_ast(mk_t(t)->get_ast(i));
        Z3_CATCH_RETURN(0);
    }

    unsigned Z3_theory_get_num_apps(Z3_theory t) {
        Z3_context c = Z3_theory_get_context(t);
        Z3_TRY;
        RESET_ERROR_CODE();
        return mk_t(t)->get_num_parents();
        Z3_CATCH_RETURN(0);
    }

    Z3_ast Z3_theory_get_app(Z3_theory t, unsigned i) {
        Z3_context c = Z3_theory_get_context(t);
        Z3_TRY;
        RESET_ERROR_CODE();
        return of_ast(mk_t(t)->get_parent(i));
        Z3_CATCH_RETURN(0);
    }

    Z3_bool Z3_theory_is_value(Z3_theory t, Z3_ast n) {
        Z3_context c = Z3_theory_get_context(t);
        Z3_TRY;
        RESET_ERROR_CODE();
        return is_app(to_ast(n)) && mk_t(t)->get_family_id() == to_app(to_ast(n))->get_family_id();
        Z3_CATCH_RETURN(Z3_FALSE);
    }

    Z3_bool Z3_theory_is_decl(Z3_theory t, Z3_func_decl d) {
        Z3_context c = Z3_theory_get_context(t);
        Z3_TRY;
        RESET_ERROR_CODE();
        return mk_t(t)->get_family_id() == to_func_decl(d)->get_family_id();
        Z3_CATCH_RETURN(Z3_FALSE);
    }

};
