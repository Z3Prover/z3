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
#include "api/z3.h"
#include "api/api_log_macros.h"
#include "api/api_context.h"
#include "api/api_util.h"
#include "parsers/util/pattern_validation.h"
#include "ast/expr_abstract.h"

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
            nullptr,
            nullptr,
            num_patterns, patterns,
            0, nullptr,
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
            SET_ERROR_CODE(Z3_SORT_ERROR, nullptr);
            return nullptr;
        }
        if (num_patterns > 0 && num_no_patterns > 0) {
            SET_ERROR_CODE(Z3_INVALID_USAGE, nullptr);
            return nullptr;
        }
        expr * const* ps = reinterpret_cast<expr * const*>(patterns);
        expr * const* no_ps = reinterpret_cast<expr * const*>(no_patterns);
        symbol qid = to_symbol(quantifier_id);
        bool is_rec = mk_c(c)->m().rec_fun_qid() == qid;
        if (!is_rec) {
            pattern_validator v(mk_c(c)->m());
            for (unsigned i = 0; i < num_patterns; i++) {
                if (!v(num_decls, ps[i], 0, 0)) {
                    SET_ERROR_CODE(Z3_INVALID_PATTERN, nullptr);
                    return nullptr;
                }
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
                is_forall ? forall_k : exists_k,
                names.size(), ts, names.c_ptr(), to_expr(body),
                weight,
                qid,
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
        Z3_CATCH_RETURN(nullptr);
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

    Z3_ast Z3_API Z3_mk_lambda(Z3_context c,
                               unsigned num_decls, Z3_sort const types[],
                               Z3_symbol const decl_names[],
                               Z3_ast body) {

        Z3_TRY;
        LOG_Z3_mk_lambda(c, num_decls, types, decl_names, body);
        RESET_ERROR_CODE();
        expr_ref result(mk_c(c)->m());
        if (num_decls == 0) {
            SET_ERROR_CODE(Z3_INVALID_USAGE, nullptr);
            RETURN_Z3(nullptr);
        }

        sort* const* ts = reinterpret_cast<sort * const*>(types);
        svector<symbol> names;
        for (unsigned i = 0; i < num_decls; ++i) {
            names.push_back(to_symbol(decl_names[i]));
        }
        result = mk_c(c)->m().mk_lambda(names.size(), ts, names.c_ptr(), to_expr(body));
        mk_c(c)->save_ast_trail(result.get());
        return of_ast(result.get());
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_lambda_const(Z3_context c, 
                                     unsigned num_decls, Z3_app const vars[],
                                     Z3_ast body) {

        Z3_TRY;
        LOG_Z3_mk_lambda_const(c, num_decls, vars, body);
        RESET_ERROR_CODE();
        if (num_decls == 0) {
            SET_ERROR_CODE(Z3_INVALID_USAGE, nullptr);
            RETURN_Z3(nullptr);
        }

        svector<symbol>  _names;
        ptr_vector<sort> _vars;
        ptr_vector<expr> _args;
        for (unsigned i = 0; i < num_decls; ++i) {
            app* a = to_app(vars[i]);
            _names.push_back(to_app(a)->get_decl()->get_name());
            _args.push_back(a);
            _vars.push_back(mk_c(c)->m().get_sort(a));
        }
        expr_ref result(mk_c(c)->m());        
        expr_abstract(mk_c(c)->m(), 0, num_decls, _args.c_ptr(), to_expr(body), result);
        
        result = mk_c(c)->m().mk_lambda(_vars.size(), _vars.c_ptr(), _names.c_ptr(), result);
        mk_c(c)->save_ast_trail(result.get());
        return of_ast(result.get());
        Z3_CATCH_RETURN(nullptr);
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
            SET_ERROR_CODE(Z3_INVALID_USAGE, nullptr);
            RETURN_Z3(nullptr);
        }
        if (num_bound == 0) {
            SET_ERROR_CODE(Z3_INVALID_USAGE, "number of bound variables is 0");
            RETURN_Z3(nullptr);
        }
        for (unsigned i = 0; i < num_bound; ++i) {
            app* a = to_app(bound[i]);
            if (a->get_kind() != AST_APP) {
                SET_ERROR_CODE(Z3_INVALID_ARG, nullptr);
                RETURN_Z3(nullptr);
            }
            symbol s(to_app(a)->get_decl()->get_name());
            names.push_back(of_symbol(s));
            types.push_back(of_sort(mk_c(c)->m().get_sort(a)));
            bound_asts.push_back(a);
            if (a->get_family_id() != null_family_id || a->get_num_args() != 0) {
                SET_ERROR_CODE(Z3_INVALID_ARG, nullptr);
                RETURN_Z3(nullptr);
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
                SET_ERROR_CODE(Z3_INVALID_ARG, nullptr);
                RETURN_Z3(nullptr);
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
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_quantifier_const(Z3_context c,
                                         Z3_bool is_forall,
                                         unsigned weight,
                                         unsigned num_bound,
                                         Z3_app const bound[],
                                         unsigned num_patterns,
                                         Z3_pattern const patterns[],
                                         Z3_ast body) {
        return Z3_mk_quantifier_const_ex(c, is_forall, weight, nullptr, nullptr,
                                         num_bound, bound,
                                         num_patterns, patterns,
                                         0, nullptr,
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
                SET_ERROR_CODE(Z3_INVALID_ARG, nullptr);
                RETURN_Z3(nullptr);
            }
        }
        app* a = mk_c(c)->m().mk_pattern(num_patterns, reinterpret_cast<app*const*>(to_exprs(terms)));
        mk_c(c)->save_ast_trail(a);
        RETURN_Z3(of_pattern(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_bound(Z3_context c, unsigned index, Z3_sort ty) {
        Z3_TRY;
        LOG_Z3_mk_bound(c, index, ty);
        RESET_ERROR_CODE();
        ast* a = mk_c(c)->m().mk_var(index, to_sort(ty));
        mk_c(c)->save_ast_trail(a);
        RETURN_Z3(of_ast(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_bool Z3_API Z3_is_quantifier_forall(Z3_context c, Z3_ast a) {
        Z3_TRY;
        LOG_Z3_is_quantifier_forall(c, a);
        RESET_ERROR_CODE();
        return ::is_forall(to_ast(a)) ? Z3_TRUE : Z3_FALSE;
        Z3_CATCH_RETURN(Z3_FALSE);
    }

    Z3_bool Z3_API Z3_is_quantifier_exists(Z3_context c, Z3_ast a) {
        Z3_TRY;
        LOG_Z3_is_quantifier_exists(c, a);
        RESET_ERROR_CODE();
        return ::is_exists(to_ast(a))  ? Z3_TRUE : Z3_FALSE;
        Z3_CATCH_RETURN(Z3_FALSE);
    }

    Z3_bool Z3_API Z3_is_lambda(Z3_context c, Z3_ast a) {
        Z3_TRY;
        LOG_Z3_is_lambda(c, a);
        RESET_ERROR_CODE();
        return ::is_lambda(to_ast(a))  ? Z3_TRUE : Z3_FALSE;
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
            SET_ERROR_CODE(Z3_SORT_ERROR, nullptr);
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
            SET_ERROR_CODE(Z3_SORT_ERROR, nullptr);
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
            SET_ERROR_CODE(Z3_SORT_ERROR, nullptr);
            RETURN_Z3(nullptr);
        }
        Z3_CATCH_RETURN(nullptr);
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
            SET_ERROR_CODE(Z3_SORT_ERROR, nullptr);
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
            SET_ERROR_CODE(Z3_SORT_ERROR, nullptr);
            RETURN_Z3(nullptr);
        }
        Z3_CATCH_RETURN(nullptr);
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
            SET_ERROR_CODE(Z3_SORT_ERROR, nullptr);
            return nullptr;
        }
        Z3_CATCH_RETURN(nullptr);
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
            SET_ERROR_CODE(Z3_SORT_ERROR, nullptr);
            RETURN_Z3(nullptr);
        }
        Z3_CATCH_RETURN(nullptr);
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
            SET_ERROR_CODE(Z3_SORT_ERROR, nullptr);
            RETURN_Z3(nullptr);
        }
        Z3_CATCH_RETURN(nullptr);
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
            SET_ERROR_CODE(Z3_SORT_ERROR, nullptr);
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
            SET_ERROR_CODE(Z3_SORT_ERROR, nullptr);
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
            SET_ERROR_CODE(Z3_SORT_ERROR, nullptr);
            RETURN_Z3(nullptr);
        }
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_pattern_to_ast(Z3_context c, Z3_pattern p) {
        RESET_ERROR_CODE();
        return (Z3_ast)(p);
    }

    Z3_API char const * Z3_pattern_to_string(Z3_context c, Z3_pattern p) {
        return Z3_ast_to_string(c, reinterpret_cast<Z3_ast>(p));
    }

};

