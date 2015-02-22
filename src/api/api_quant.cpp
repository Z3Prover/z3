/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    api_quant.cpp

Abstract:
    API for quantifiers

Author:

    Leonardo de Moura (leonardo) 2012-02-29.

Revision History:

--*/
#include<iostream>
#include"z3.h"
#include"api_log_macros.h"
#include"api_context.h"
#include"api_util.h"
#include"pattern_validation.h"
#include"expr_abstract.h"

extern "C" {

    Z3_ast Z3_API Z3_mk_quantifier(
        Z3_context c, 
        Z3_bool is_forall, 
        unsigned weight, 
        unsigned num_patterns, Z3_pattern const patterns[], 
        unsigned num_decls, Z3_sort const sorts[], 
        Z3_symbol const decl_names[], 
        Z3_ast body) 
    {
        return Z3_mk_quantifier_ex(
            c, 
            is_forall, 
            weight,
            0,
            0,
            num_patterns, patterns,
            0, 0,
            num_decls, sorts,
            decl_names,
            body
            );

    }

    Z3_ast mk_quantifier_ex_core(
        Z3_context c, 
        Z3_bool is_forall, 
        unsigned weight, 
        Z3_symbol quantifier_id,
        Z3_symbol skolem_id,
        unsigned num_patterns, Z3_pattern const patterns[], 
        unsigned num_no_patterns, Z3_ast const no_patterns[], 
        unsigned num_decls, Z3_sort const sorts[], 
        Z3_symbol const decl_names[], 
        Z3_ast body) {
        Z3_TRY;
        RESET_ERROR_CODE();
        if (!mk_c(c)->m().is_bool(to_expr(body))) {
            SET_ERROR_CODE(Z3_SORT_ERROR);
        }
        if (num_patterns > 0 && num_no_patterns > 0) {
            SET_ERROR_CODE(Z3_INVALID_USAGE);
        }
        expr * const* ps = reinterpret_cast<expr * const*>(patterns);
        expr * const* no_ps = reinterpret_cast<expr * const*>(no_patterns);
        pattern_validator v(mk_c(c)->m());
        for (unsigned i = 0; i < num_patterns; i++) {
            if (!v(num_decls, ps[i])) {
                SET_ERROR_CODE(Z3_INVALID_PATTERN);
                return 0;
            }
        }

        sort* const* ts = reinterpret_cast<sort * const*>(sorts);
        svector<symbol> names;
        for (unsigned i = 0; i < num_decls; ++i) {
            names.push_back(to_symbol(decl_names[i]));
        }
        expr_ref result(mk_c(c)->m());
        if (num_decls > 0) {
            result = mk_c(c)->m().mk_quantifier(
                (0 != is_forall), 
                names.size(), ts, names.c_ptr(), to_expr(body),            
                weight, 
                to_symbol(quantifier_id),
                to_symbol(skolem_id),
                num_patterns, ps,
                num_no_patterns, no_ps
                );
        }
        else {
            result = to_expr(body);
        }
        mk_c(c)->save_ast_trail(result.get());
        return of_ast(result.get());
        Z3_CATCH_RETURN(0);
    }

    Z3_ast Z3_API Z3_mk_quantifier_ex(
        Z3_context c, 
        Z3_bool is_forall, 
        unsigned weight, 
        Z3_symbol quantifier_id,
        Z3_symbol skolem_id,
        unsigned num_patterns, Z3_pattern const patterns[], 
        unsigned num_no_patterns, Z3_ast const no_patterns[], 
        unsigned num_decls, Z3_sort const sorts[], 
        Z3_symbol const decl_names[], 
        Z3_ast body)
    {
        LOG_Z3_mk_quantifier_ex(c, is_forall, weight, quantifier_id, skolem_id, num_patterns, patterns, 
                                num_no_patterns, no_patterns, num_decls, sorts, decl_names, body);
        Z3_ast r = mk_quantifier_ex_core(c, is_forall, weight, quantifier_id, skolem_id, num_patterns, patterns, 
                                         num_no_patterns, no_patterns, num_decls, sorts, decl_names, body);
        RETURN_Z3(r);
    }
    
    Z3_ast Z3_API Z3_mk_forall(Z3_context c, 
                               unsigned weight, 
                               unsigned num_patterns, Z3_pattern const patterns[], 
                               unsigned num_decls, Z3_sort const types[], 
                               Z3_symbol const decl_names[], 
                               Z3_ast body) {
        return Z3_mk_quantifier(c, 1, weight, num_patterns, patterns, num_decls, types, decl_names, body);
    }
    
    Z3_ast Z3_API Z3_mk_exists(Z3_context c, 
                               unsigned weight, 
                               unsigned num_patterns, Z3_pattern const patterns[], 
                               unsigned num_decls, Z3_sort const types[], 
                               Z3_symbol const decl_names[], 
                               Z3_ast body) {
        return Z3_mk_quantifier(c, 0, weight, num_patterns, patterns, num_decls, types, decl_names, body);
    }


    Z3_ast Z3_API Z3_mk_quantifier_const_ex(Z3_context c, 
                                            Z3_bool is_forall,
                                            unsigned weight,
                                            Z3_symbol quantifier_id,
                                            Z3_symbol skolem_id,
                                            unsigned num_bound,
                                            Z3_app const bound[],
                                            unsigned num_patterns,
                                            Z3_pattern const patterns[],
                                            unsigned num_no_patterns,
                                            Z3_ast const no_patterns[],
                                            Z3_ast body) {
        Z3_TRY;
        LOG_Z3_mk_quantifier_const_ex(c, is_forall, weight, quantifier_id, skolem_id, num_bound, bound, num_patterns, patterns,
                                      num_no_patterns, no_patterns, body);
        RESET_ERROR_CODE();
        svector<Z3_symbol> names;
        svector<Z3_sort> types;
        ptr_vector<expr> bound_asts;
        if (num_patterns > 0 && num_no_patterns > 0) {
            SET_ERROR_CODE(Z3_INVALID_USAGE);
        }
        for (unsigned i = 0; i < num_bound; ++i) {
            app* a = to_app(bound[i]);
            if (a->get_kind() != AST_APP) {
                SET_ERROR_CODE(Z3_INVALID_ARG);
                RETURN_Z3(0);
            }
            symbol s(to_app(a)->get_decl()->get_name());
            names.push_back(of_symbol(s));
            types.push_back(of_sort(mk_c(c)->m().get_sort(a)));
            bound_asts.push_back(a);
            if (a->get_family_id() != null_family_id || a->get_num_args() != 0) {
                SET_ERROR_CODE(Z3_INVALID_ARG);
                RETURN_Z3(0);
            }
        }
        // Abstract patterns
        svector<Z3_pattern> _patterns;
        expr_ref_vector pinned(mk_c(c)->m());
        for (unsigned i = 0; i < num_patterns; ++i) {
            expr_ref result(mk_c(c)->m());
            app* pat = to_pattern(patterns[i]);
            SASSERT(mk_c(c)->m().is_pattern(pat));
            expr_abstract(mk_c(c)->m(), 0, num_bound, bound_asts.c_ptr(), pat, result);
            SASSERT(result.get()->get_kind() == AST_APP);        
            pinned.push_back(result.get());
            SASSERT(mk_c(c)->m().is_pattern(result.get()));
            _patterns.push_back(of_pattern(result.get()));
        }
        svector<Z3_ast> _no_patterns;
        for (unsigned i = 0; i < num_no_patterns; ++i) {
            expr_ref result(mk_c(c)->m());
            if (!is_app(to_expr(no_patterns[i]))) {
                SET_ERROR_CODE(Z3_INVALID_ARG);
                RETURN_Z3(0);
            }
            app* pat = to_app(to_expr(no_patterns[i]));
            expr_abstract(mk_c(c)->m(), 0, num_bound, bound_asts.c_ptr(), pat, result);
            SASSERT(result.get()->get_kind() == AST_APP);        
            pinned.push_back(result.get());
            _no_patterns.push_back(of_ast(result.get()));
        }
        expr_ref abs_body(mk_c(c)->m());
        expr_abstract(mk_c(c)->m(), 0, num_bound, bound_asts.c_ptr(), to_expr(body), abs_body);

        Z3_ast result = mk_quantifier_ex_core(c, is_forall, weight, 
                                              quantifier_id,
                                              skolem_id,
                                              num_patterns, _patterns.c_ptr(), 
                                              num_no_patterns, _no_patterns.c_ptr(),
                                              names.size(), types.c_ptr(), names.c_ptr(), 
                                              of_ast(abs_body.get()));
        RETURN_Z3(result);
        Z3_CATCH_RETURN(0);
    }

    Z3_ast Z3_API Z3_mk_quantifier_const(Z3_context c, 
                                         Z3_bool is_forall,
                                         unsigned weight,
                                         unsigned num_bound,
                                         Z3_app const bound[],
                                         unsigned num_patterns,
                                         Z3_pattern const patterns[],
                                         Z3_ast body) {
        return Z3_mk_quantifier_const_ex(c, is_forall, weight, 0, 0, 
                                         num_bound, bound, 
                                         num_patterns, patterns,
                                         0, 0,
                                         body);
    }

    Z3_ast Z3_API Z3_mk_forall_const(Z3_context c, 
                                     unsigned weight,
                                     unsigned num_bound,
                                     Z3_app const bound[],
                                     unsigned num_patterns,
                                     Z3_pattern const patterns[],
                                     Z3_ast body) {
        return Z3_mk_quantifier_const(c, true, weight, num_bound, bound, num_patterns, patterns, body);
    }

    Z3_ast Z3_API Z3_mk_exists_const(Z3_context c, 
                                     unsigned weight,
                                     unsigned num_bound,
                                     Z3_app const bound[],
                                     unsigned num_patterns,
                                     Z3_pattern const patterns[],
                                     Z3_ast body) {
        return Z3_mk_quantifier_const(c, false, weight, num_bound, bound, num_patterns, patterns, body);
    }
    
    Z3_pattern Z3_API Z3_mk_pattern(Z3_context c, unsigned num_patterns, Z3_ast const terms[]) {
        Z3_TRY;
        LOG_Z3_mk_pattern(c, num_patterns, terms);
        RESET_ERROR_CODE();
        for (unsigned i = 0; i < num_patterns; ++i) {
            if (!is_app(to_expr(terms[i]))) {
                SET_ERROR_CODE(Z3_INVALID_ARG);
                RETURN_Z3(0);
            }
        }
        app* a = mk_c(c)->m().mk_pattern(num_patterns, reinterpret_cast<app*const*>(to_exprs(terms)));
        mk_c(c)->save_ast_trail(a);
        RETURN_Z3(of_pattern(a));
        Z3_CATCH_RETURN(0);
    }
    
    Z3_ast Z3_API Z3_mk_bound(Z3_context c, unsigned index, Z3_sort ty) {
        Z3_TRY;
        LOG_Z3_mk_bound(c, index, ty);
        RESET_ERROR_CODE();
        ast* a = mk_c(c)->m().mk_var(index, to_sort(ty));
        mk_c(c)->save_ast_trail(a);
        RETURN_Z3(of_ast(a));
        Z3_CATCH_RETURN(0);
    }

    Z3_bool Z3_API Z3_is_quantifier_forall(Z3_context c, Z3_ast a) {
        Z3_TRY;
        LOG_Z3_is_quantifier_forall(c, a);
        RESET_ERROR_CODE();
        ast * _a = to_ast(a);
        if (_a->get_kind() == AST_QUANTIFIER) {
            return to_quantifier(_a)->is_forall();
        }
        else {
            SET_ERROR_CODE(Z3_SORT_ERROR);
            return Z3_FALSE;
        }
        Z3_CATCH_RETURN(Z3_FALSE);
    }

    unsigned Z3_API Z3_get_quantifier_weight(Z3_context c, Z3_ast a) {
        Z3_TRY;
        LOG_Z3_get_quantifier_weight(c, a);
        RESET_ERROR_CODE();
        ast * _a = to_ast(a);
        if (_a->get_kind() == AST_QUANTIFIER) {
            return to_quantifier(_a)->get_weight();
        }
        else {
            SET_ERROR_CODE(Z3_SORT_ERROR);
            return 0;
        }
        Z3_CATCH_RETURN(0);
    }

    unsigned Z3_API Z3_get_quantifier_num_patterns(Z3_context c, Z3_ast a) {
        Z3_TRY;
        LOG_Z3_get_quantifier_num_patterns(c, a);
        RESET_ERROR_CODE();
        ast * _a = to_ast(a);
        if (_a->get_kind() == AST_QUANTIFIER) {
            return to_quantifier(_a)->get_num_patterns();
        }
        else {
            SET_ERROR_CODE(Z3_SORT_ERROR);
            return 0;
        }
        Z3_CATCH_RETURN(0);
    }

    Z3_pattern Z3_API Z3_get_quantifier_pattern_ast(Z3_context c, Z3_ast a, unsigned i) {
        Z3_TRY;
        LOG_Z3_get_quantifier_pattern_ast(c, a, i);
        RESET_ERROR_CODE();
        ast * _a = to_ast(a);
        if (_a->get_kind() == AST_QUANTIFIER) {
            Z3_pattern r = of_pattern(to_quantifier(_a)->get_patterns()[i]);
            RETURN_Z3(r);
        }
        else {
            SET_ERROR_CODE(Z3_SORT_ERROR);
            RETURN_Z3(0);
        }
        Z3_CATCH_RETURN(0);
    }


    unsigned Z3_API Z3_get_quantifier_num_no_patterns(Z3_context c, Z3_ast a) {
        Z3_TRY;
        LOG_Z3_get_quantifier_num_no_patterns(c, a);
        RESET_ERROR_CODE();
        ast * _a = to_ast(a);
        if (_a->get_kind() == AST_QUANTIFIER) {
            return to_quantifier(_a)->get_num_no_patterns();
        }
        else {
            SET_ERROR_CODE(Z3_SORT_ERROR);
            return 0;
        }
        Z3_CATCH_RETURN(0);
    }

    Z3_ast Z3_API Z3_get_quantifier_no_pattern_ast(Z3_context c, Z3_ast a, unsigned i) {
        Z3_TRY;
        LOG_Z3_get_quantifier_no_pattern_ast(c, a, i);
        RESET_ERROR_CODE();
        ast * _a = to_ast(a);
        if (_a->get_kind() == AST_QUANTIFIER) {
            Z3_ast r = of_ast(to_quantifier(_a)->get_no_pattern(i));
            RETURN_Z3(r);
        }
        else {
            SET_ERROR_CODE(Z3_SORT_ERROR);
            RETURN_Z3(0);
        }
        Z3_CATCH_RETURN(0);
    }

    Z3_symbol Z3_API Z3_get_quantifier_bound_name(Z3_context c, Z3_ast a, unsigned i) {
        Z3_TRY;
        LOG_Z3_get_quantifier_bound_name(c, a, i);
        RESET_ERROR_CODE();
        ast * _a = to_ast(a);
        if (_a->get_kind() == AST_QUANTIFIER) {
            return of_symbol(to_quantifier(_a)->get_decl_names()[i]);
        }
        else {
            SET_ERROR_CODE(Z3_SORT_ERROR);
            return 0;
        }
        Z3_CATCH_RETURN(0);
    }

    Z3_sort Z3_API Z3_get_quantifier_bound_sort(Z3_context c, Z3_ast a, unsigned i) {
        Z3_TRY;
        LOG_Z3_get_quantifier_bound_sort(c, a, i);
        RESET_ERROR_CODE();
        ast * _a = to_ast(a);
        if (_a->get_kind() == AST_QUANTIFIER) {
            Z3_sort r = of_sort(to_quantifier(_a)->get_decl_sort(i));
            RETURN_Z3(r);
        }
        else {
            SET_ERROR_CODE(Z3_SORT_ERROR);
            RETURN_Z3(0);
        }
        Z3_CATCH_RETURN(0);
    }

    Z3_ast Z3_API Z3_get_quantifier_body(Z3_context c, Z3_ast a) {
        Z3_TRY;
        LOG_Z3_get_quantifier_body(c, a);
        RESET_ERROR_CODE();
        ast * _a = to_ast(a);
        if (_a->get_kind() == AST_QUANTIFIER) {
            Z3_ast r = of_ast(to_quantifier(_a)->get_expr());
            RETURN_Z3(r);
        }
        else {
            SET_ERROR_CODE(Z3_SORT_ERROR);
            RETURN_Z3(0);
        }
        Z3_CATCH_RETURN(0);
    }

    unsigned Z3_API Z3_get_quantifier_num_bound(Z3_context c, Z3_ast a) {
        Z3_TRY;
        LOG_Z3_get_quantifier_num_bound(c, a);
        RESET_ERROR_CODE();
        ast * _a = to_ast(a);
        if (_a->get_kind() == AST_QUANTIFIER) {

            return to_quantifier(_a)->get_num_decls();
        }
        else {
            SET_ERROR_CODE(Z3_SORT_ERROR);
            return 0;
        }        
        Z3_CATCH_RETURN(0);
    }

    unsigned Z3_API Z3_get_pattern_num_terms(Z3_context c, Z3_pattern p) {
        Z3_TRY;
        LOG_Z3_get_pattern_num_terms(c, p);
        RESET_ERROR_CODE();
        app* _p = to_pattern(p);
        if (mk_c(c)->m().is_pattern(_p)) {
            return _p->get_num_args();
        }
        else {
            SET_ERROR_CODE(Z3_SORT_ERROR);
            return 0;            
        }
        Z3_CATCH_RETURN(0);
    }

    Z3_ast Z3_API Z3_get_pattern(Z3_context c, Z3_pattern p, unsigned idx) {
        Z3_TRY;
        LOG_Z3_get_pattern(c, p, idx);
        RESET_ERROR_CODE();
        app* _p = to_pattern(p);
        if (mk_c(c)->m().is_pattern(_p)) {
            Z3_ast r = of_ast(_p->get_arg(idx));
            RETURN_Z3(r);
        }
        else {
            SET_ERROR_CODE(Z3_SORT_ERROR);
            RETURN_Z3(0);
        }
        Z3_CATCH_RETURN(0);
    }

    Z3_func_decl Z3_API Z3_mk_injective_function(Z3_context c, 
                                                 Z3_symbol s, 
                                                 unsigned domain_size, 
                                                 Z3_sort const domain[],
                                                 Z3_sort range) {
        Z3_TRY;
        LOG_Z3_mk_injective_function(c, s, domain_size, domain, range);
        RESET_ERROR_CODE(); 
        ast_manager & m = mk_c(c)->m();
        mk_c(c)->reset_last_result();
        sort* range_ = to_sort(range);
        func_decl* d = m.mk_func_decl(to_symbol(s), domain_size, to_sorts(domain), range_);
        expr_ref_vector args(m);
        expr_ref fn(m), body(m);
        vector<symbol> names;
        for (unsigned i = 0; i < domain_size; ++i) {
            unsigned idx = domain_size-i-1;
            args.push_back(m.mk_var(idx, to_sort(domain[i])));
            names.push_back(symbol(idx));
        }
        fn = m.mk_app(d, args.size(), args.c_ptr());

        for (unsigned i = 0; i < domain_size; ++i) {
            expr* arg = args[i].get();
            sort* dom = m.get_sort(arg);
            func_decl* inv = m.mk_fresh_func_decl(symbol("inv"), to_symbol(s), 1, &range_, dom);
            body = m.mk_eq(m.mk_app(inv, fn.get()), arg);
            body = m.mk_forall(args.size(), to_sorts(domain), names.c_ptr(), body.get());
            mk_c(c)->save_multiple_ast_trail(body.get());
            mk_c(c)->assert_cnstr(body.get());
        }
        mk_c(c)->save_multiple_ast_trail(d);       
        RETURN_Z3(of_func_decl(d));
        Z3_CATCH_RETURN(0);
    }

    Z3_ast Z3_API Z3_pattern_to_ast(Z3_context c, Z3_pattern p) { 
        RESET_ERROR_CODE();
        return (Z3_ast)(p); 
    }    

    Z3_API char const * Z3_pattern_to_string(Z3_context c, Z3_pattern p) {
        return Z3_ast_to_string(c, reinterpret_cast<Z3_ast>(p));
    }
    
};
