/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    api_ast.cpp

Abstract:
    Basic API for ASTs

Author:

    Leonardo de Moura (leonardo) 2012-02-29.

Revision History:

--*/
#include<iostream>
#include "api/api_log_macros.h"
#include "api/api_context.h"
#include "api/api_util.h"
#include "ast/well_sorted.h"
#include "ast/arith_decl_plugin.h"
#include "ast/bv_decl_plugin.h"
#include "ast/datatype_decl_plugin.h"
#include "ast/array_decl_plugin.h"
#include "ast/pb_decl_plugin.h"
#include "ast/ast_translation.h"
#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include "ast/ast_smt_pp.h"
#include "ast/ast_smt2_pp.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/rewriter/var_subst.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "ast/rewriter/recfun_replace.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/pp.h"
#include "util/scoped_ctrl_c.h"
#include "util/cancel_eh.h"
#include "util/scoped_timer.h"
#include "ast/pp_params.hpp"
#include "ast/expr_abstract.h"


extern bool is_numeral_sort(Z3_context c, Z3_sort ty);

extern "C" {

    Z3_symbol Z3_API Z3_mk_int_symbol(Z3_context c, int i) {
        Z3_TRY;
        LOG_Z3_mk_int_symbol(c, i);
        RESET_ERROR_CODE();
        if (i < 0 || (size_t)i >= (SIZE_MAX >> PTR_ALIGNMENT)) {
            SET_ERROR_CODE(Z3_IOB, nullptr);
            return of_symbol(symbol::null);
        }
        Z3_symbol result = of_symbol(symbol((unsigned)i));
        return result;
        Z3_CATCH_RETURN(of_symbol(symbol::null));
    }

    Z3_symbol Z3_API Z3_mk_string_symbol(Z3_context c, char const * str) {
        Z3_TRY;
        LOG_Z3_mk_string_symbol(c, str);
        RESET_ERROR_CODE();
        symbol s;
        if (str == nullptr || *str == 0)
            s = symbol::null;
        else
            s = symbol(str);
        Z3_symbol result = of_symbol(s);
        return result;
        Z3_CATCH_RETURN(of_symbol(symbol::null));
    }

    bool Z3_API Z3_is_eq_sort(Z3_context c, Z3_sort s1, Z3_sort s2) {
        RESET_ERROR_CODE();
        return s1 == s2;
    }

    Z3_sort Z3_API Z3_mk_uninterpreted_sort(Z3_context c, Z3_symbol name) {
        Z3_TRY;
        LOG_Z3_mk_uninterpreted_sort(c, name);
        RESET_ERROR_CODE();
        sort* ty = mk_c(c)->m().mk_uninterpreted_sort(to_symbol(name));
        mk_c(c)->save_ast_trail(ty);
        RETURN_Z3(of_sort(ty));
        Z3_CATCH_RETURN(nullptr);
    }

    bool Z3_API Z3_is_eq_ast(Z3_context c, Z3_ast s1, Z3_ast s2) {
        RESET_ERROR_CODE();
        return s1 == s2;
    }

    bool Z3_API Z3_is_eq_func_decl(Z3_context c, Z3_func_decl s1, Z3_func_decl s2) {
        RESET_ERROR_CODE();
        return s1 == s2;
    }

    Z3_func_decl Z3_API Z3_mk_func_decl(Z3_context c, Z3_symbol s, unsigned domain_size, Z3_sort const* domain,
                                        Z3_sort range) {
        Z3_TRY;
        LOG_Z3_mk_func_decl(c, s, domain_size, domain, range);
        RESET_ERROR_CODE();
        func_decl* d = mk_c(c)->m().mk_func_decl(to_symbol(s),
                                                 domain_size,
                                                 to_sorts(domain),
                                                 to_sort(range));

        mk_c(c)->save_ast_trail(d);
        RETURN_Z3(of_func_decl(d));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_func_decl Z3_API Z3_mk_rec_func_decl(Z3_context c, Z3_symbol s, unsigned domain_size, Z3_sort const* domain,
                                            Z3_sort range) {
        Z3_TRY;
        LOG_Z3_mk_rec_func_decl(c, s, domain_size, domain, range);
        RESET_ERROR_CODE();
        // 
        recfun::promise_def def = 
            mk_c(c)->recfun().get_plugin().mk_def(to_symbol(s),                                      
                                          domain_size,
                                          to_sorts(domain),
                                          to_sort(range));
        func_decl* d = def.get_def()->get_decl();
        mk_c(c)->save_ast_trail(d);
        RETURN_Z3(of_func_decl(d));
        Z3_CATCH_RETURN(nullptr);
    }

    void Z3_API Z3_add_rec_def(Z3_context c, Z3_func_decl f, unsigned n, Z3_ast args[], Z3_ast body) {
        Z3_TRY;
        LOG_Z3_add_rec_def(c, f, n, args, body);
        func_decl* d = to_func_decl(f);
        ast_manager& m = mk_c(c)->m();
        recfun::decl::plugin& p = mk_c(c)->recfun().get_plugin();
        expr_ref abs_body(m);
        expr_ref_vector _args(m);
        var_ref_vector _vars(m);
        for (unsigned i = 0; i < n; ++i) {
            _args.push_back(to_expr(args[i]));
            _vars.push_back(m.mk_var(n - i - 1, _args.back()->get_sort()));
            if (_args.back()->get_sort() != d->get_domain(i)) {
                SET_ERROR_CODE(Z3_INVALID_ARG, nullptr);            
                return;            
            }
        }
        expr_abstract(m, 0, n, _args.data(), to_expr(body), abs_body);
        recfun::promise_def pd = p.get_promise_def(d);
        if (!pd.get_def()) {
            SET_ERROR_CODE(Z3_INVALID_ARG, nullptr);
            return;
        }
        if (abs_body->get_sort() != d->get_range()) {
            SET_ERROR_CODE(Z3_INVALID_ARG, nullptr);            
            return;
        }
        recfun_replace replace(m);
        p.set_definition(replace, pd, n, _vars.data(), abs_body);
        Z3_CATCH;
    }

    Z3_ast Z3_API Z3_mk_app(Z3_context c, Z3_func_decl d, unsigned num_args, Z3_ast const * args) {
        Z3_TRY;
        LOG_Z3_mk_app(c, d, num_args, args);
        RESET_ERROR_CODE();
        ptr_buffer<expr> arg_list;
        for (unsigned i = 0; i < num_args; ++i) {
            arg_list.push_back(to_expr(args[i]));
        }
        func_decl* _d = reinterpret_cast<func_decl*>(d);
        app* a = mk_c(c)->m().mk_app(_d, num_args, arg_list.data());
        mk_c(c)->save_ast_trail(a);
        check_sorts(c, a);
        RETURN_Z3(of_ast(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_const(Z3_context c, Z3_symbol s, Z3_sort ty) {
        Z3_TRY;
        LOG_Z3_mk_const(c, s, ty);
        RESET_ERROR_CODE();
        app* a = mk_c(c)->m().mk_const(mk_c(c)->m().mk_const_decl(to_symbol(s), to_sort(ty)));
        mk_c(c)->save_ast_trail(a);
        RETURN_Z3(of_ast(a));
        Z3_CATCH_RETURN(nullptr);
    }


    Z3_func_decl Z3_API Z3_mk_fresh_func_decl(Z3_context c, const char * prefix, unsigned domain_size,
                                              Z3_sort const domain[], Z3_sort range) {
        Z3_TRY;
        LOG_Z3_mk_fresh_func_decl(c, prefix, domain_size, domain, range);
        RESET_ERROR_CODE();
        if (prefix == nullptr) {
            prefix = "";
        }

        func_decl* d = mk_c(c)->m().mk_fresh_func_decl(prefix,
                                                       domain_size,
                                                       reinterpret_cast<sort*const*>(domain),
                                                       to_sort(range), false);

        mk_c(c)->save_ast_trail(d);
        RETURN_Z3(of_func_decl(d));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_fresh_const(Z3_context c, const char * prefix, Z3_sort ty) {
        Z3_TRY;
        LOG_Z3_mk_fresh_const(c, prefix, ty);
        RESET_ERROR_CODE();
        if (prefix == nullptr) {
            prefix = "";
        }
        app* a = mk_c(c)->m().mk_fresh_const(prefix, to_sort(ty), false);
        mk_c(c)->save_ast_trail(a);
        RETURN_Z3(of_ast(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_true(Z3_context c) {
        Z3_TRY;
        LOG_Z3_mk_true(c);
        RESET_ERROR_CODE();
        Z3_ast r = of_ast(mk_c(c)->m().mk_true());
        RETURN_Z3(r);
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_false(Z3_context c) {
        Z3_TRY;
        LOG_Z3_mk_false(c);
        RESET_ERROR_CODE();
        Z3_ast r = of_ast(mk_c(c)->m().mk_false());
        RETURN_Z3(r);
        Z3_CATCH_RETURN(nullptr);
    }

    MK_UNARY(Z3_mk_not, mk_c(c)->get_basic_fid(), OP_NOT, SKIP);
    MK_BINARY(Z3_mk_eq, mk_c(c)->get_basic_fid(), OP_EQ, SKIP);
    MK_NARY(Z3_mk_distinct, mk_c(c)->get_basic_fid(), OP_DISTINCT, SKIP);
    MK_BINARY(Z3_mk_iff, mk_c(c)->get_basic_fid(), OP_EQ, SKIP);
    MK_BINARY(Z3_mk_implies, mk_c(c)->get_basic_fid(), OP_IMPLIES, SKIP);
    MK_BINARY(Z3_mk_xor, mk_c(c)->get_basic_fid(), OP_XOR, SKIP);
    MK_NARY(Z3_mk_and, mk_c(c)->get_basic_fid(), OP_AND, SKIP);
    MK_NARY(Z3_mk_or, mk_c(c)->get_basic_fid(), OP_OR, SKIP);

    Z3_ast mk_ite_core(Z3_context c, Z3_ast t1, Z3_ast t2, Z3_ast t3) {
        expr * result = mk_c(c)->m().mk_ite(to_expr(t1), to_expr(t2), to_expr(t3));
        mk_c(c)->save_ast_trail(result);
        check_sorts(c, result);
        return of_ast(result);
    }

    Z3_ast Z3_API Z3_mk_ite(Z3_context c, Z3_ast t1, Z3_ast t2, Z3_ast t3) {
        Z3_TRY;
        LOG_Z3_mk_ite(c, t1, t2, t3);
        RESET_ERROR_CODE();
        Z3_ast r = mk_ite_core(c, t1, t2, t3);
        RETURN_Z3(r);
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_sort Z3_API Z3_mk_bool_sort(Z3_context c) {
        Z3_TRY;
        LOG_Z3_mk_bool_sort(c);
        RESET_ERROR_CODE();
        Z3_sort r = of_sort(mk_c(c)->m().mk_sort(mk_c(c)->m().get_basic_family_id(), BOOL_SORT));
        RETURN_Z3(r);
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_app_to_ast(Z3_context c, Z3_app a) {
        RESET_ERROR_CODE();
        return (Z3_ast)(a);
    }

    Z3_ast Z3_API Z3_sort_to_ast(Z3_context c, Z3_sort s) {
        RESET_ERROR_CODE();
        return (Z3_ast)(s);
    }

    Z3_ast Z3_API Z3_func_decl_to_ast(Z3_context c, Z3_func_decl f) {
        RESET_ERROR_CODE();
        return (Z3_ast)(f);
    }

    // ------------------------

    unsigned Z3_API Z3_get_ast_id(Z3_context c, Z3_ast t) {
        LOG_Z3_get_ast_id(c, t);
        RESET_ERROR_CODE();
        return to_expr(t)->get_id();
    }

    unsigned Z3_API Z3_get_func_decl_id(Z3_context c, Z3_func_decl f) {
        LOG_Z3_get_func_decl_id(c, f);
        RESET_ERROR_CODE();
        return to_func_decl(f)->get_id();
    }

    unsigned Z3_API Z3_get_sort_id(Z3_context c, Z3_sort s) {
        LOG_Z3_get_sort_id(c, s);
        RESET_ERROR_CODE();
        return to_sort(s)->get_id();
    }

    bool Z3_API Z3_is_well_sorted(Z3_context c, Z3_ast t) {
        Z3_TRY;
        LOG_Z3_is_well_sorted(c, t);
        RESET_ERROR_CODE();
        return is_well_sorted(mk_c(c)->m(), to_expr(t));
        Z3_CATCH_RETURN(false);
    }

    Z3_symbol_kind Z3_API Z3_get_symbol_kind(Z3_context c, Z3_symbol s) {
        Z3_TRY;
        LOG_Z3_get_symbol_kind(c, s);
        RESET_ERROR_CODE();
        symbol _s = to_symbol(s);
        return _s.is_numerical() ? Z3_INT_SYMBOL : Z3_STRING_SYMBOL;
        Z3_CATCH_RETURN(Z3_INT_SYMBOL);
    }

    int Z3_API Z3_get_symbol_int(Z3_context c, Z3_symbol s) {
        Z3_TRY;
        LOG_Z3_get_symbol_int(c, s);
        RESET_ERROR_CODE();
        symbol _s = to_symbol(s);
        if (_s.is_numerical()) {
            return _s.get_num();
        }
        SET_ERROR_CODE(Z3_INVALID_ARG, nullptr);
        return -1;
        Z3_CATCH_RETURN(-1);
    }

    Z3_API char const * Z3_get_symbol_string(Z3_context c, Z3_symbol s) {
        Z3_TRY;
        LOG_Z3_get_symbol_string(c, s);
        RESET_ERROR_CODE();
        symbol _s = to_symbol(s);
        if (_s.is_numerical()) {
            std::ostringstream buffer;
            buffer << _s.get_num();
            return mk_c(c)->mk_external_string(buffer.str());
        }
        else {
            return mk_c(c)->mk_external_string(_s.bare_str());
        }
        Z3_CATCH_RETURN("");
    }

    Z3_ast_kind Z3_API Z3_get_ast_kind(Z3_context c, Z3_ast a) {
        Z3_TRY;
        LOG_Z3_get_ast_kind(c, a);
        RESET_ERROR_CODE();
        CHECK_VALID_AST(a, Z3_UNKNOWN_AST);
        ast * _a = to_expr(a);
        switch (_a->get_kind()) {
        case AST_APP: {
            expr * e = to_expr(_a);
            // Real algebraic numbers are not considered Z3_NUMERAL_AST
            if (is_numeral_sort(c, of_sort(e->get_sort())) && mk_c(c)->m().is_unique_value(e))
                return Z3_NUMERAL_AST;
            return Z3_APP_AST;
        }
        case AST_VAR:        return Z3_VAR_AST;
        case AST_QUANTIFIER: return Z3_QUANTIFIER_AST;
        case AST_SORT:       return Z3_SORT_AST;
        case AST_FUNC_DECL:  return Z3_FUNC_DECL_AST;
        default:             return Z3_UNKNOWN_AST;
        }
        Z3_CATCH_RETURN(Z3_UNKNOWN_AST);
    }

    unsigned Z3_API Z3_get_ast_hash(Z3_context c, Z3_ast a) {
        LOG_Z3_get_ast_hash(c, a);
        RESET_ERROR_CODE();
        return to_ast(a)->hash();
    }

    bool Z3_API Z3_is_app(Z3_context c, Z3_ast a) {
        LOG_Z3_is_app(c, a);
        RESET_ERROR_CODE();
        return a != nullptr && is_app(reinterpret_cast<ast*>(a));
    }

    Z3_app Z3_API Z3_to_app(Z3_context c, Z3_ast a) {
        LOG_Z3_to_app(c, a);
        RESET_ERROR_CODE();
        SASSERT(is_app(reinterpret_cast<ast*>(a)));
        RETURN_Z3(of_app(reinterpret_cast<app*>(a)));
    }

    Z3_func_decl Z3_API Z3_to_func_decl(Z3_context c, Z3_ast a) {
        LOG_Z3_to_func_decl(c, a);
        RESET_ERROR_CODE();
        SASSERT(is_func_decl(reinterpret_cast<ast*>(a)));
        RETURN_Z3(of_func_decl(reinterpret_cast<func_decl*>(a)));
    }

    Z3_func_decl Z3_API Z3_get_app_decl(Z3_context c, Z3_app a) {
        LOG_Z3_get_app_decl(c, a);
        RESET_ERROR_CODE();
        if (!is_app(reinterpret_cast<ast*>(a))) {
            SET_ERROR_CODE(Z3_INVALID_ARG, nullptr);
            RETURN_Z3(nullptr);
        }
        RETURN_Z3(of_func_decl(to_app(a)->get_decl()));
    }

    unsigned Z3_API Z3_get_app_num_args(Z3_context c, Z3_app a) {
        LOG_Z3_get_app_num_args(c, a);
        RESET_ERROR_CODE();
        return to_app(a)->get_num_args();
    }

    Z3_ast Z3_API Z3_get_app_arg(Z3_context c, Z3_app a, unsigned i) {
        LOG_Z3_get_app_arg(c, a, i);
        RESET_ERROR_CODE();
        if (!is_app(reinterpret_cast<ast*>(a))) {
            SET_ERROR_CODE(Z3_INVALID_ARG, nullptr);
            RETURN_Z3(nullptr);
        }
        if (i >= to_app(a)->get_num_args()) {
            SET_ERROR_CODE(Z3_IOB, nullptr);
            RETURN_Z3(nullptr);
        }
        RETURN_Z3(of_ast(to_app(a)->get_arg(i)));
    }

    Z3_symbol Z3_API Z3_get_decl_name(Z3_context c, Z3_func_decl d) {
        LOG_Z3_get_decl_name(c, d);
        RESET_ERROR_CODE();
        CHECK_VALID_AST(d, of_symbol(symbol::null));
        return of_symbol(to_func_decl(d)->get_name());
    }

    unsigned Z3_API Z3_get_decl_num_parameters(Z3_context c, Z3_func_decl d) {
        LOG_Z3_get_decl_num_parameters(c, d);
        RESET_ERROR_CODE();
        CHECK_VALID_AST(d, 0);
        return to_func_decl(d)->get_num_parameters();
    }

    Z3_parameter_kind Z3_API Z3_get_decl_parameter_kind(Z3_context c, Z3_func_decl d, unsigned idx) {
        Z3_TRY;
        LOG_Z3_get_decl_parameter_kind(c, d, idx);
        RESET_ERROR_CODE();
        CHECK_VALID_AST(d, Z3_PARAMETER_INT);
        if (idx >= to_func_decl(d)->get_num_parameters()) {
            SET_ERROR_CODE(Z3_IOB, nullptr);
            return Z3_PARAMETER_INT;
        }
        parameter const& p = to_func_decl(d)->get_parameters()[idx];
        if (p.is_int()) {
            return Z3_PARAMETER_INT;
        }
        if (p.is_double()) {
            return Z3_PARAMETER_DOUBLE;
        }
        if (p.is_symbol()) {
            return Z3_PARAMETER_SYMBOL;
        }
        if (p.is_rational()) {
            return Z3_PARAMETER_RATIONAL;
        }
        if (p.is_ast() && is_sort(p.get_ast())) {
            return Z3_PARAMETER_SORT;
        }
        if (p.is_ast() && is_expr(p.get_ast())) {
            return Z3_PARAMETER_AST;
        }
        SASSERT(p.is_ast() && is_func_decl(p.get_ast()));
        return Z3_PARAMETER_FUNC_DECL;
        Z3_CATCH_RETURN(Z3_PARAMETER_INT);
    }

    int Z3_API Z3_get_decl_int_parameter(Z3_context c, Z3_func_decl d, unsigned idx) {
        Z3_TRY;
        LOG_Z3_get_decl_int_parameter(c, d, idx);
        RESET_ERROR_CODE();
        CHECK_VALID_AST(d, 0);
        if (idx >= to_func_decl(d)->get_num_parameters()) {
            SET_ERROR_CODE(Z3_IOB, nullptr);
            return 0;
        }
        parameter const& p = to_func_decl(d)->get_parameters()[idx];
        if (!p.is_int()) {
            SET_ERROR_CODE(Z3_INVALID_ARG, nullptr);
            return 0;
        }
        return p.get_int();
        Z3_CATCH_RETURN(0);
    }

    double Z3_API Z3_get_decl_double_parameter(Z3_context c, Z3_func_decl d, unsigned idx) {
        Z3_TRY;
        LOG_Z3_get_decl_double_parameter(c, d, idx);
        RESET_ERROR_CODE();
        CHECK_VALID_AST(d, 0);
        if (idx >= to_func_decl(d)->get_num_parameters()) {
            SET_ERROR_CODE(Z3_IOB, nullptr);
            return 0;
        }
        parameter const& p = to_func_decl(d)->get_parameters()[idx];
        if (!p.is_double()) {
            SET_ERROR_CODE(Z3_INVALID_ARG, nullptr);
            return 0;
        }
        return p.get_double();
        Z3_CATCH_RETURN(0.0);
    }

    Z3_symbol Z3_API Z3_get_decl_symbol_parameter(Z3_context c, Z3_func_decl d, unsigned idx) {
        Z3_TRY;
        LOG_Z3_get_decl_symbol_parameter(c, d, idx);
        RESET_ERROR_CODE();
        CHECK_VALID_AST(d, of_symbol(symbol::null));
        if (idx >= to_func_decl(d)->get_num_parameters()) {
            SET_ERROR_CODE(Z3_IOB, nullptr);
            return of_symbol(symbol::null);
        }
        parameter const& p = to_func_decl(d)->get_parameters()[idx];
        if (!p.is_symbol()) {
            SET_ERROR_CODE(Z3_INVALID_ARG, nullptr);
            return of_symbol(symbol::null);
        }
        return of_symbol(p.get_symbol());
        Z3_CATCH_RETURN(of_symbol(symbol::null));
    }

    Z3_sort Z3_API Z3_get_decl_sort_parameter(Z3_context c, Z3_func_decl d, unsigned idx) {
        Z3_TRY;
        LOG_Z3_get_decl_sort_parameter(c, d, idx);
        RESET_ERROR_CODE();
        CHECK_VALID_AST(d, nullptr);
        if (idx >= to_func_decl(d)->get_num_parameters()) {
            SET_ERROR_CODE(Z3_IOB, nullptr);
            RETURN_Z3(nullptr);
        }
        parameter const& p = to_func_decl(d)->get_parameters()[idx];
        if (!p.is_ast() || !is_sort(p.get_ast())) {
            SET_ERROR_CODE(Z3_INVALID_ARG, nullptr);
            RETURN_Z3(nullptr);
        }
        RETURN_Z3(of_sort(to_sort(p.get_ast())));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_get_decl_ast_parameter(Z3_context c, Z3_func_decl d, unsigned idx) {
        Z3_TRY;
        LOG_Z3_get_decl_ast_parameter(c, d, idx);
        RESET_ERROR_CODE();
        CHECK_VALID_AST(d, nullptr);
        if (idx >= to_func_decl(d)->get_num_parameters()) {
            SET_ERROR_CODE(Z3_IOB, nullptr);
            RETURN_Z3(nullptr);
        }
        parameter const& p = to_func_decl(d)->get_parameters()[idx];
        if (!p.is_ast()) {
            SET_ERROR_CODE(Z3_INVALID_ARG, nullptr);
            RETURN_Z3(nullptr);
        }
        RETURN_Z3(of_ast(p.get_ast()));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_func_decl Z3_API Z3_get_decl_func_decl_parameter(Z3_context c, Z3_func_decl d, unsigned idx) {
        Z3_TRY;
        LOG_Z3_get_decl_func_decl_parameter(c, d, idx);
        RESET_ERROR_CODE();
        CHECK_VALID_AST(d, nullptr);
        if (idx >= to_func_decl(d)->get_num_parameters()) {
            SET_ERROR_CODE(Z3_IOB, nullptr);
            RETURN_Z3(nullptr);
        }
        parameter const& p = to_func_decl(d)->get_parameters()[idx];
        if (!p.is_ast() || !is_func_decl(p.get_ast())) {
            SET_ERROR_CODE(Z3_INVALID_ARG, nullptr);
            RETURN_Z3(nullptr);
        }
        RETURN_Z3(of_func_decl(to_func_decl(p.get_ast())));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_string Z3_API Z3_get_decl_rational_parameter(Z3_context c, Z3_func_decl d, unsigned idx) {
        Z3_TRY;
        LOG_Z3_get_decl_rational_parameter(c, d, idx);
        RESET_ERROR_CODE();
        CHECK_VALID_AST(d, "");
        if (idx >= to_func_decl(d)->get_num_parameters()) {
            SET_ERROR_CODE(Z3_IOB, nullptr);
            return "";
        }
        parameter const& p = to_func_decl(d)->get_parameters()[idx];
        if (!p.is_rational()) {
            SET_ERROR_CODE(Z3_INVALID_ARG, nullptr);
            return "";
        }
        return mk_c(c)->mk_external_string(p.get_rational().to_string());
        Z3_CATCH_RETURN("");
    }


    Z3_symbol Z3_API Z3_get_sort_name(Z3_context c, Z3_sort t) {
        Z3_TRY;
        LOG_Z3_get_sort_name(c, t);
        RESET_ERROR_CODE();
        CHECK_VALID_AST(t, of_symbol(symbol::null));
        return of_symbol(to_sort(t)->get_name());
        Z3_CATCH_RETURN(of_symbol(symbol::null));
    }

    Z3_sort Z3_API Z3_get_sort(Z3_context c, Z3_ast a) {
        Z3_TRY;
        LOG_Z3_get_sort(c, a);
        RESET_ERROR_CODE();
        CHECK_IS_EXPR(a, nullptr);
        Z3_sort r = of_sort(to_expr(a)->get_sort());
        RETURN_Z3(r);
        Z3_CATCH_RETURN(nullptr);
    }

    unsigned Z3_API Z3_get_arity(Z3_context c, Z3_func_decl d) {
        Z3_TRY;
        LOG_Z3_get_arity(c, d);
        RESET_ERROR_CODE();
        CHECK_VALID_AST(d, 0);
        return to_func_decl(d)->get_arity();
        Z3_CATCH_RETURN(0);
    }

    unsigned Z3_API Z3_get_domain_size(Z3_context c, Z3_func_decl d) {
        Z3_TRY;
        LOG_Z3_get_domain_size(c, d);
        RESET_ERROR_CODE();
        CHECK_VALID_AST(d, 0);
        return to_func_decl(d)->get_arity();
        Z3_CATCH_RETURN(0);
    }

    Z3_sort Z3_API Z3_get_domain(Z3_context c, Z3_func_decl d, unsigned i) {
        Z3_TRY;
        LOG_Z3_get_domain(c, d, i);
        RESET_ERROR_CODE();
        CHECK_VALID_AST(d, nullptr);
        if (i >= to_func_decl(d)->get_arity()) {
            SET_ERROR_CODE(Z3_IOB, nullptr);
            RETURN_Z3(nullptr);
        }
        Z3_sort r = of_sort(to_func_decl(d)->get_domain(i));
        RETURN_Z3(r);
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_sort Z3_API Z3_get_range(Z3_context c, Z3_func_decl d) {
        Z3_TRY;
        LOG_Z3_get_range(c, d);
        RESET_ERROR_CODE();
        CHECK_VALID_AST(d, nullptr);
        Z3_sort r = of_sort(to_func_decl(d)->get_range());
        RETURN_Z3(r);
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_sort_kind Z3_get_sort_kind(Z3_context c, Z3_sort t) {
        LOG_Z3_get_sort_kind(c, t);
        RESET_ERROR_CODE();
        CHECK_VALID_AST(t, Z3_UNKNOWN_SORT);
        family_id fid = to_sort(t)->get_family_id();
        decl_kind k   = to_sort(t)->get_decl_kind();
        if (mk_c(c)->m().is_uninterp(to_sort(t))) {
            return Z3_UNINTERPRETED_SORT;
        }
        else if (fid == mk_c(c)->m().get_basic_family_id() && k == BOOL_SORT) {
            return Z3_BOOL_SORT;
        }
        else if (fid == mk_c(c)->get_arith_fid() && k == INT_SORT) {
            return Z3_INT_SORT;
        }
        else if (fid == mk_c(c)->get_arith_fid() && k == REAL_SORT) {
            return Z3_REAL_SORT;
        }
        else if (fid == mk_c(c)->get_bv_fid() && k == BV_SORT) {
            return Z3_BV_SORT;
        }
        else if (fid == mk_c(c)->get_array_fid() && k == ARRAY_SORT) {
            return Z3_ARRAY_SORT;
        }
        else if (fid == mk_c(c)->get_dt_fid() && k == DATATYPE_SORT) {
            return Z3_DATATYPE_SORT;
        }
        else if (fid == mk_c(c)->get_datalog_fid() && k == datalog::DL_RELATION_SORT) {
            return Z3_RELATION_SORT;
        }
        else if (fid == mk_c(c)->get_datalog_fid() && k == datalog::DL_FINITE_SORT) {
            return Z3_FINITE_DOMAIN_SORT;
        }
        else if (fid == mk_c(c)->get_fpa_fid() && k == FLOATING_POINT_SORT) {
            return Z3_FLOATING_POINT_SORT;
        }
        else if (fid == mk_c(c)->get_fpa_fid() && k == ROUNDING_MODE_SORT) {
            return Z3_ROUNDING_MODE_SORT;
        }
        else if (fid == mk_c(c)->get_seq_fid() && k == SEQ_SORT) {
            return Z3_SEQ_SORT;
        }
        else if (fid == mk_c(c)->get_seq_fid() && k == RE_SORT) {
            return Z3_RE_SORT;
        }
        else {
            return Z3_UNKNOWN_SORT;
        }
    }

    Z3_lbool Z3_API Z3_get_bool_value(Z3_context c, Z3_ast a) {
        Z3_TRY;
        LOG_Z3_get_bool_value(c, a);
        RESET_ERROR_CODE();
        CHECK_IS_EXPR(a, Z3_L_UNDEF);
        ast_manager & m = mk_c(c)->m();
        ast * n         = to_ast(a);
        if (m.is_true(to_expr(n)))
            return Z3_L_TRUE;
        if (m.is_false(to_expr(n)))
            return Z3_L_FALSE;
        return Z3_L_UNDEF;
        Z3_CATCH_RETURN(Z3_L_UNDEF);
    }


    static Z3_ast simplify(Z3_context c, Z3_ast _a, Z3_params _p) {
        Z3_TRY;
        RESET_ERROR_CODE();
        ast_manager & m = mk_c(c)->m();
        expr * a = to_expr(_a);
        auto &p = to_param_ref(_p);
        unsigned timeout     = p.get_uint("timeout", mk_c(c)->get_timeout());
        bool     use_ctrl_c  = p.get_bool("ctrl_c", false);
        th_rewriter m_rw(m, p);
        m_rw.set_solver(alloc(api::seq_expr_solver, m, p));
        expr_ref    result(m);
        cancel_eh<reslimit> eh(m.limit());
        api::context::set_interruptable si(*(mk_c(c)), eh);
        {
            scoped_ctrl_c ctrlc(eh, false, use_ctrl_c);
            scoped_timer timer(timeout, &eh);
            try {
                m_rw(a, result);
            }
            catch (z3_exception & ex) {
                mk_c(c)->handle_exception(ex);
                return nullptr;
            }
        }
        mk_c(c)->save_ast_trail(result);
        return of_ast(result.get());
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_simplify(Z3_context c, Z3_ast _a) {
        LOG_Z3_simplify(c, _a);
        RETURN_Z3(simplify(c, _a, nullptr));
    }

    Z3_ast Z3_API Z3_simplify_ex(Z3_context c, Z3_ast _a, Z3_params p) {
        LOG_Z3_simplify_ex(c, _a, p);
        RETURN_Z3(simplify(c, _a, p));
    }

    Z3_string Z3_API Z3_simplify_get_help(Z3_context c) {
        Z3_TRY;
        LOG_Z3_simplify_get_help(c);
        RESET_ERROR_CODE();
        std::ostringstream buffer;
        param_descrs descrs;
        th_rewriter::get_param_descrs(descrs);
        descrs.display(buffer);
        return mk_c(c)->mk_external_string(buffer.str());
        Z3_CATCH_RETURN("");
    }

    Z3_param_descrs Z3_API Z3_simplify_get_param_descrs(Z3_context c) {
        Z3_TRY;
        LOG_Z3_simplify_get_param_descrs(c);
        RESET_ERROR_CODE();
        Z3_param_descrs_ref * d = alloc(Z3_param_descrs_ref, *mk_c(c));
        mk_c(c)->save_object(d);
        th_rewriter::get_param_descrs(d->m_descrs);
        Z3_param_descrs r = of_param_descrs(d);
        RETURN_Z3(r);
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_update_term(Z3_context c, Z3_ast _a, unsigned num_args, Z3_ast const _args[]) {
        Z3_TRY;
        LOG_Z3_update_term(c, _a, num_args, _args);
        RESET_ERROR_CODE();
        ast_manager& m = mk_c(c)->m();
        expr* a = to_expr(_a);
        expr* const* args = to_exprs(num_args, _args);
        switch(a->get_kind()) {
        case AST_APP: {
            app* e = to_app(a);
            if (e->get_num_args() != num_args) {
                SET_ERROR_CODE(Z3_IOB, nullptr);
            }
            else {
                a = m.mk_app(e->get_decl(), num_args, args);
            }
            break;
        }
        case AST_QUANTIFIER: {
            if (num_args != 1) {
                SET_ERROR_CODE(Z3_IOB, nullptr);
            }
            else {
                a = m.update_quantifier(to_quantifier(a), args[0]);
            }
            break;
        }
        default:
            break;
        }
        mk_c(c)->save_ast_trail(a);
        RETURN_Z3(of_expr(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_substitute(Z3_context c,
                                Z3_ast _a,
                                unsigned num_exprs,
                                Z3_ast const _from[],
                                Z3_ast const _to[]) {
        Z3_TRY;
        LOG_Z3_substitute(c, _a, num_exprs, _from, _to);
        RESET_ERROR_CODE();
        ast_manager & m = mk_c(c)->m();
        expr * a = to_expr(_a);
        expr * const * from = to_exprs(num_exprs, _from);
        expr * const * to   = to_exprs(num_exprs, _to);
        expr * r = nullptr;
        for (unsigned i = 0; i < num_exprs; i++) {
            if (from[i]->get_sort() != to[i]->get_sort()) {
                SET_ERROR_CODE(Z3_SORT_ERROR, nullptr);
                RETURN_Z3(of_expr(nullptr));
            }
            SASSERT(from[i]->get_ref_count() > 0);
            SASSERT(to[i]->get_ref_count() > 0);
        }
        expr_safe_replace subst(m);
        for (unsigned i = 0; i < num_exprs; i++) {
            subst.insert(from[i], to[i]);
        }
        expr_ref   new_a(m);
        subst(a, new_a);
        mk_c(c)->save_ast_trail(new_a);
        r = new_a.get();
        RETURN_Z3(of_expr(r));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_substitute_vars(Z3_context c,
                                     Z3_ast _a,
                                     unsigned num_exprs,
                                     Z3_ast const _to[]) {
        Z3_TRY;
        LOG_Z3_substitute_vars(c, _a, num_exprs, _to);
        RESET_ERROR_CODE();
        ast_manager & m = mk_c(c)->m();
        expr * a = to_expr(_a);
        expr * const * to   = to_exprs(num_exprs, _to);
        var_subst subst(m, false);
        expr_ref new_a = subst(a, num_exprs, to);
        mk_c(c)->save_ast_trail(new_a);
        RETURN_Z3(of_expr(new_a.get()));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_API char const * Z3_ast_to_string(Z3_context c, Z3_ast a) {
        Z3_TRY;
        LOG_Z3_ast_to_string(c, a);
        RESET_ERROR_CODE();
        std::ostringstream buffer;
        switch (mk_c(c)->get_print_mode()) {
        case Z3_PRINT_SMTLIB_FULL: {
            params_ref p;
            p.set_uint("max_depth", 4294967295u);
            p.set_uint("min_alias_size", 4294967295u);
            buffer << mk_pp(to_ast(a), mk_c(c)->m(), p);
            break;
        }
        case Z3_PRINT_LOW_LEVEL:
            buffer << mk_ll_pp(to_ast(a), mk_c(c)->m());
            break;
        case Z3_PRINT_SMTLIB2_COMPLIANT: 
            buffer << mk_ismt2_pp(to_ast(a), mk_c(c)->m());
            break;
        default:
            UNREACHABLE();
        }
        return mk_c(c)->mk_external_string(buffer.str());
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_API char const * Z3_sort_to_string(Z3_context c, Z3_sort s) {
        return Z3_ast_to_string(c, reinterpret_cast<Z3_ast>(s));
    }

    Z3_API char const * Z3_func_decl_to_string(Z3_context c, Z3_func_decl f) {
        return Z3_ast_to_string(c, reinterpret_cast<Z3_ast>(f));
    }

    Z3_string Z3_API Z3_benchmark_to_smtlib_string(Z3_context c,
                                                   Z3_string name,
                                                   Z3_string logic,
                                                   Z3_string status,
                                                   Z3_string attributes,
                                                   unsigned num_assumptions,
                                                   Z3_ast const assumptions[],
                                                   Z3_ast formula) {
        Z3_TRY;
        LOG_Z3_benchmark_to_smtlib_string(c, name, logic, status, attributes, num_assumptions, assumptions, formula);
        RESET_ERROR_CODE();
        std::ostringstream buffer;
        ast_smt_pp pp(mk_c(c)->m());
        pp.set_benchmark_name(name);
        pp.set_logic(logic?symbol(logic):symbol::null);
        pp.set_status(status);
        pp.add_attributes(attributes);
        pp_params params;
        pp.set_simplify_implies(params.simplify_implies());
        for (unsigned i = 0; i < num_assumptions; ++i) {
            pp.add_assumption(to_expr(assumptions[i]));
        }
        pp.display_smt2(buffer, to_expr(formula));
        return mk_c(c)->mk_external_string(buffer.str());
        Z3_CATCH_RETURN("");
    }

    Z3_decl_kind Z3_API Z3_get_decl_kind(Z3_context c, Z3_func_decl d) {
        Z3_TRY;
        LOG_Z3_get_decl_kind(c, d);
        RESET_ERROR_CODE();
        func_decl* _d = to_func_decl(d);

        if (d == nullptr || null_family_id == _d->get_family_id()) {
            return Z3_OP_UNINTERPRETED;
        }
        if (mk_c(c)->get_basic_fid() == _d->get_family_id()) {
            switch(_d->get_decl_kind()) {
            case OP_TRUE:     return Z3_OP_TRUE;
            case OP_FALSE:    return Z3_OP_FALSE;
            case OP_EQ:       return Z3_OP_EQ;
            case OP_DISTINCT: return Z3_OP_DISTINCT;
            case OP_ITE:      return Z3_OP_ITE;
            case OP_AND:      return Z3_OP_AND;
            case OP_OR:       return Z3_OP_OR;
            case OP_XOR:      return Z3_OP_XOR;
            case OP_NOT:      return Z3_OP_NOT;
            case OP_IMPLIES:  return Z3_OP_IMPLIES;
            case OP_OEQ:      return Z3_OP_OEQ;

            case PR_UNDEF:    return Z3_OP_PR_UNDEF;
            case PR_TRUE:     return Z3_OP_PR_TRUE;
            case PR_ASSERTED: return Z3_OP_PR_ASSERTED;
            case PR_GOAL:     return Z3_OP_PR_GOAL;
            case PR_MODUS_PONENS: return Z3_OP_PR_MODUS_PONENS;
            case PR_REFLEXIVITY: return Z3_OP_PR_REFLEXIVITY;
            case PR_SYMMETRY: return Z3_OP_PR_SYMMETRY;
            case PR_TRANSITIVITY: return Z3_OP_PR_TRANSITIVITY;
            case PR_TRANSITIVITY_STAR: return Z3_OP_PR_TRANSITIVITY_STAR;
            case PR_MONOTONICITY: return Z3_OP_PR_MONOTONICITY;
            case PR_QUANT_INTRO: return Z3_OP_PR_QUANT_INTRO;
            case PR_BIND: return Z3_OP_PR_BIND;
            case PR_DISTRIBUTIVITY: return Z3_OP_PR_DISTRIBUTIVITY;
            case PR_AND_ELIM: return Z3_OP_PR_AND_ELIM;
            case PR_NOT_OR_ELIM: return Z3_OP_PR_NOT_OR_ELIM;
            case PR_REWRITE: return Z3_OP_PR_REWRITE;
            case PR_REWRITE_STAR: return Z3_OP_PR_REWRITE_STAR;
            case PR_PULL_QUANT: return Z3_OP_PR_PULL_QUANT;
            case PR_PUSH_QUANT: return Z3_OP_PR_PUSH_QUANT;
            case PR_ELIM_UNUSED_VARS: return Z3_OP_PR_ELIM_UNUSED_VARS;
            case PR_DER: return Z3_OP_PR_DER;
            case PR_QUANT_INST: return Z3_OP_PR_QUANT_INST;
            case PR_HYPOTHESIS: return Z3_OP_PR_HYPOTHESIS;
            case PR_LEMMA: return Z3_OP_PR_LEMMA;
            case PR_UNIT_RESOLUTION: return Z3_OP_PR_UNIT_RESOLUTION;
            case PR_IFF_TRUE: return Z3_OP_PR_IFF_TRUE;
            case PR_IFF_FALSE: return Z3_OP_PR_IFF_FALSE;
            case PR_COMMUTATIVITY: return Z3_OP_PR_COMMUTATIVITY;
            case PR_DEF_AXIOM: return Z3_OP_PR_DEF_AXIOM;
            case PR_ASSUMPTION_ADD: return Z3_OP_PR_ASSUMPTION_ADD;
            case PR_LEMMA_ADD: return Z3_OP_PR_LEMMA_ADD;
            case PR_REDUNDANT_DEL: return Z3_OP_PR_REDUNDANT_DEL;
            case PR_CLAUSE_TRAIL: return Z3_OP_PR_CLAUSE_TRAIL;
            case PR_DEF_INTRO: return Z3_OP_PR_DEF_INTRO;
            case PR_APPLY_DEF: return Z3_OP_PR_APPLY_DEF;
            case PR_IFF_OEQ: return Z3_OP_PR_IFF_OEQ;
            case PR_NNF_POS: return Z3_OP_PR_NNF_POS;
            case PR_NNF_NEG: return Z3_OP_PR_NNF_NEG;
            case PR_SKOLEMIZE:  return Z3_OP_PR_SKOLEMIZE;
            case PR_MODUS_PONENS_OEQ: return Z3_OP_PR_MODUS_PONENS_OEQ;
            case PR_TH_LEMMA: return Z3_OP_PR_TH_LEMMA;
            case PR_HYPER_RESOLVE: return Z3_OP_PR_HYPER_RESOLVE;
            default:
                return Z3_OP_INTERNAL;
            }
        }
        if (mk_c(c)->get_arith_fid() == _d->get_family_id()) {
            switch(_d->get_decl_kind()) {
            case OP_NUM: return Z3_OP_ANUM;
            case OP_IRRATIONAL_ALGEBRAIC_NUM: return Z3_OP_AGNUM;
            case OP_LE: return Z3_OP_LE;
            case OP_GE: return Z3_OP_GE;
            case OP_LT: return Z3_OP_LT;
            case OP_GT: return Z3_OP_GT;
            case OP_ADD: return Z3_OP_ADD;
            case OP_SUB: return Z3_OP_SUB;
            case OP_UMINUS: return Z3_OP_UMINUS;
            case OP_MUL: return Z3_OP_MUL;
            case OP_DIV: return Z3_OP_DIV;
            case OP_IDIV: return Z3_OP_IDIV;
            case OP_REM: return Z3_OP_REM;
            case OP_MOD: return Z3_OP_MOD;
            case OP_POWER: return Z3_OP_POWER;
            case OP_TO_REAL: return Z3_OP_TO_REAL;
            case OP_TO_INT: return Z3_OP_TO_INT;
            case OP_IS_INT: return Z3_OP_IS_INT;
            default:
                return Z3_OP_INTERNAL;
            }
        }
        if (mk_c(c)->get_array_fid() == _d->get_family_id()) {
            switch(_d->get_decl_kind()) {
            case OP_STORE: return Z3_OP_STORE;
            case OP_SELECT: return Z3_OP_SELECT;
            case OP_CONST_ARRAY: return Z3_OP_CONST_ARRAY;
            case OP_ARRAY_DEFAULT: return Z3_OP_ARRAY_DEFAULT;
            case OP_ARRAY_MAP: return Z3_OP_ARRAY_MAP;
            case OP_SET_UNION: return Z3_OP_SET_UNION;
            case OP_SET_INTERSECT: return Z3_OP_SET_INTERSECT;
            case OP_SET_DIFFERENCE: return Z3_OP_SET_DIFFERENCE;
            case OP_SET_COMPLEMENT: return Z3_OP_SET_COMPLEMENT;
            case OP_SET_SUBSET: return Z3_OP_SET_SUBSET;
            case OP_AS_ARRAY: return Z3_OP_AS_ARRAY;
            case OP_ARRAY_EXT: return Z3_OP_ARRAY_EXT;
            case OP_SET_CARD: return Z3_OP_SET_CARD;
            case OP_SET_HAS_SIZE: return Z3_OP_SET_HAS_SIZE;
            default:
                return Z3_OP_INTERNAL;
            }
        }

        if (mk_c(c)->get_special_relations_fid() == _d->get_family_id()) {
            switch(_d->get_decl_kind()) {
            case OP_SPECIAL_RELATION_LO : return Z3_OP_SPECIAL_RELATION_LO;
            case OP_SPECIAL_RELATION_PO : return Z3_OP_SPECIAL_RELATION_PO;
            case OP_SPECIAL_RELATION_PLO: return Z3_OP_SPECIAL_RELATION_PLO;
            case OP_SPECIAL_RELATION_TO : return Z3_OP_SPECIAL_RELATION_TO;
            case OP_SPECIAL_RELATION_TC : return Z3_OP_SPECIAL_RELATION_TC;
            default: UNREACHABLE();
            }
        }


        if (mk_c(c)->get_bv_fid() == _d->get_family_id()) {
            switch(_d->get_decl_kind()) {
            case OP_BV_NUM: return Z3_OP_BNUM;
            case OP_BIT1: return Z3_OP_BIT1;
            case OP_BIT0: return Z3_OP_BIT0;
            case OP_BNEG: return Z3_OP_BNEG;
            case OP_BADD: return Z3_OP_BADD;
            case OP_BSUB: return Z3_OP_BSUB;
            case OP_BMUL: return Z3_OP_BMUL;
            case OP_BSDIV: return Z3_OP_BSDIV;
            case OP_BUDIV: return Z3_OP_BUDIV;
            case OP_BSREM: return Z3_OP_BSREM;
            case OP_BUREM: return Z3_OP_BUREM;
            case OP_BSMOD: return Z3_OP_BSMOD;
            case OP_BSDIV0: return Z3_OP_BSDIV0;
            case OP_BUDIV0: return Z3_OP_BUDIV0;
            case OP_BSREM0: return Z3_OP_BUREM0;
            case OP_BUREM0: return Z3_OP_BUREM0;
            case OP_BSMOD0: return Z3_OP_BSMOD0;
            case OP_ULEQ:   return Z3_OP_ULEQ;
            case OP_SLEQ:   return Z3_OP_SLEQ;
            case OP_UGEQ:   return Z3_OP_UGEQ;
            case OP_SGEQ:   return Z3_OP_SGEQ;
            case OP_ULT:  return Z3_OP_ULT;
            case OP_SLT:  return Z3_OP_SLT;
            case OP_UGT:  return Z3_OP_UGT;
            case OP_SGT:  return Z3_OP_SGT;
            case OP_BAND:     return Z3_OP_BAND;
            case OP_BOR:      return Z3_OP_BOR;
            case OP_BNOT:     return Z3_OP_BNOT;
            case OP_BXOR:     return Z3_OP_BXOR;
            case OP_BNAND:    return Z3_OP_BNAND;
            case OP_BNOR:     return Z3_OP_BNOR;
            case OP_BXNOR:    return Z3_OP_BXNOR;
            case OP_CONCAT:   return Z3_OP_CONCAT;
            case OP_SIGN_EXT: return Z3_OP_SIGN_EXT;
            case OP_ZERO_EXT: return Z3_OP_ZERO_EXT;
            case OP_EXTRACT:  return Z3_OP_EXTRACT;
            case OP_REPEAT:       return Z3_OP_REPEAT;
            case OP_BREDOR:       return Z3_OP_BREDOR;
            case OP_BREDAND:      return Z3_OP_BREDAND;
            case OP_BCOMP:        return Z3_OP_BCOMP;
            case OP_BSHL:         return Z3_OP_BSHL;
            case OP_BLSHR:        return Z3_OP_BLSHR;
            case OP_BASHR:        return Z3_OP_BASHR;
            case OP_ROTATE_LEFT:  return Z3_OP_ROTATE_LEFT;
            case OP_ROTATE_RIGHT: return Z3_OP_ROTATE_RIGHT;
            case OP_EXT_ROTATE_LEFT:  return Z3_OP_EXT_ROTATE_LEFT;
            case OP_EXT_ROTATE_RIGHT: return Z3_OP_EXT_ROTATE_RIGHT;
            case OP_INT2BV:    return Z3_OP_INT2BV;
            case OP_BV2INT:    return Z3_OP_BV2INT;
            case OP_CARRY:     return Z3_OP_CARRY;
            case OP_XOR3:      return Z3_OP_XOR3;
            case OP_BIT2BOOL: return Z3_OP_BIT2BOOL;
            case OP_BSMUL_NO_OVFL: return Z3_OP_BSMUL_NO_OVFL;
            case OP_BUMUL_NO_OVFL: return Z3_OP_BUMUL_NO_OVFL;
            case OP_BSMUL_NO_UDFL: return Z3_OP_BSMUL_NO_UDFL;
            case OP_BSDIV_I: return Z3_OP_BSDIV_I;
            case OP_BUDIV_I: return Z3_OP_BUDIV_I;
            case OP_BSREM_I: return Z3_OP_BSREM_I;
            case OP_BUREM_I: return Z3_OP_BUREM_I;
            case OP_BSMOD_I: return Z3_OP_BSMOD_I;
            default:
                return Z3_OP_INTERNAL;
            }
        }
        if (mk_c(c)->get_dt_fid() == _d->get_family_id()) {
            switch(_d->get_decl_kind()) {
            case OP_DT_CONSTRUCTOR:  return Z3_OP_DT_CONSTRUCTOR;
            case OP_DT_RECOGNISER:   return Z3_OP_DT_RECOGNISER;
            case OP_DT_IS:           return Z3_OP_DT_IS;
            case OP_DT_ACCESSOR:     return Z3_OP_DT_ACCESSOR;
            case OP_DT_UPDATE_FIELD: return Z3_OP_DT_UPDATE_FIELD;
            default:
                return Z3_OP_INTERNAL;
            }
        }
        if (mk_c(c)->get_datalog_fid() == _d->get_family_id()) {
            switch(_d->get_decl_kind()) {
            case datalog::OP_RA_STORE: return Z3_OP_RA_STORE;
            case datalog::OP_RA_EMPTY: return Z3_OP_RA_EMPTY;
            case datalog::OP_RA_IS_EMPTY: return Z3_OP_RA_IS_EMPTY;
            case datalog::OP_RA_JOIN: return Z3_OP_RA_JOIN;
            case datalog::OP_RA_UNION: return Z3_OP_RA_UNION;
            case datalog::OP_RA_WIDEN: return Z3_OP_RA_WIDEN;
            case datalog::OP_RA_PROJECT: return Z3_OP_RA_PROJECT;
            case datalog::OP_RA_FILTER: return Z3_OP_RA_FILTER;
            case datalog::OP_RA_NEGATION_FILTER: return Z3_OP_RA_NEGATION_FILTER;
            case datalog::OP_RA_RENAME: return Z3_OP_RA_RENAME;
            case datalog::OP_RA_COMPLEMENT: return Z3_OP_RA_COMPLEMENT;
            case datalog::OP_RA_SELECT: return Z3_OP_RA_SELECT;
            case datalog::OP_RA_CLONE:  return Z3_OP_RA_CLONE;
            case datalog::OP_DL_CONSTANT: return Z3_OP_FD_CONSTANT;
            case datalog::OP_DL_LT: return Z3_OP_FD_LT;
            default:
                return Z3_OP_INTERNAL;
            }
        }

        if (mk_c(c)->get_seq_fid() == _d->get_family_id()) {
            switch (_d->get_decl_kind()) {
            case OP_SEQ_UNIT: return Z3_OP_SEQ_UNIT;
            case OP_SEQ_EMPTY: return Z3_OP_SEQ_EMPTY;
            case OP_SEQ_CONCAT: return Z3_OP_SEQ_CONCAT;
            case OP_SEQ_PREFIX: return Z3_OP_SEQ_PREFIX;
            case OP_SEQ_SUFFIX: return Z3_OP_SEQ_SUFFIX;
            case OP_SEQ_CONTAINS: return Z3_OP_SEQ_CONTAINS;
            case OP_SEQ_EXTRACT: return Z3_OP_SEQ_EXTRACT;
            case OP_SEQ_REPLACE: return Z3_OP_SEQ_REPLACE;
            case OP_SEQ_AT: return Z3_OP_SEQ_AT;
            case OP_SEQ_NTH: return Z3_OP_SEQ_NTH;
            case OP_SEQ_LENGTH: return Z3_OP_SEQ_LENGTH;
            case OP_SEQ_INDEX: return Z3_OP_SEQ_INDEX;
            case OP_SEQ_TO_RE: return Z3_OP_SEQ_TO_RE;
            case OP_SEQ_IN_RE: return Z3_OP_SEQ_IN_RE;

            case _OP_STRING_STRREPL: return Z3_OP_SEQ_REPLACE;
            case _OP_STRING_CONCAT: return Z3_OP_SEQ_CONCAT;
            case _OP_STRING_LENGTH: return Z3_OP_SEQ_LENGTH;
            case _OP_STRING_STRCTN: return Z3_OP_SEQ_CONTAINS;
            case _OP_STRING_PREFIX: return Z3_OP_SEQ_PREFIX;
            case _OP_STRING_SUFFIX: return Z3_OP_SEQ_SUFFIX;
            case _OP_STRING_IN_REGEXP: return Z3_OP_SEQ_IN_RE;
            case _OP_STRING_TO_REGEXP: return Z3_OP_SEQ_TO_RE;
            case _OP_STRING_CHARAT: return Z3_OP_SEQ_AT;
            case _OP_STRING_SUBSTR: return Z3_OP_SEQ_EXTRACT;
            case _OP_STRING_STRIDOF: return Z3_OP_SEQ_INDEX;
            case _OP_REGEXP_EMPTY: return Z3_OP_RE_EMPTY_SET;
            case _OP_REGEXP_FULL_CHAR: return Z3_OP_RE_FULL_SET;

            case OP_STRING_STOI: return Z3_OP_STR_TO_INT;
            case OP_STRING_ITOS: return Z3_OP_INT_TO_STR;
            case OP_STRING_LT: return Z3_OP_STRING_LT;
            case OP_STRING_LE: return Z3_OP_STRING_LE;

            case OP_RE_PLUS: return Z3_OP_RE_PLUS;
            case OP_RE_STAR: return Z3_OP_RE_STAR;
            case OP_RE_OPTION: return Z3_OP_RE_OPTION;
            case OP_RE_CONCAT: return Z3_OP_RE_CONCAT;
            case OP_RE_UNION: return Z3_OP_RE_UNION;
            case OP_RE_INTERSECT: return Z3_OP_RE_INTERSECT;
            case OP_RE_LOOP: return Z3_OP_RE_LOOP;
            case OP_RE_FULL_SEQ_SET: return Z3_OP_RE_FULL_SET;
            //case OP_RE_FULL_CHAR_SET: return Z3_OP_RE_FULL_SET;
            case OP_RE_EMPTY_SET: return Z3_OP_RE_EMPTY_SET;
            default:
                return Z3_OP_INTERNAL;
            }
        }

        if (mk_c(c)->get_fpa_fid() == _d->get_family_id()) {
            switch (_d->get_decl_kind()) {
            case OP_FPA_RM_NEAREST_TIES_TO_EVEN: return Z3_OP_FPA_RM_NEAREST_TIES_TO_EVEN;
            case OP_FPA_RM_NEAREST_TIES_TO_AWAY: return Z3_OP_FPA_RM_NEAREST_TIES_TO_AWAY;
            case OP_FPA_RM_TOWARD_POSITIVE: return Z3_OP_FPA_RM_TOWARD_POSITIVE;
            case OP_FPA_RM_TOWARD_NEGATIVE: return Z3_OP_FPA_RM_TOWARD_NEGATIVE;
            case OP_FPA_RM_TOWARD_ZERO: return Z3_OP_FPA_RM_TOWARD_ZERO;
            case OP_FPA_NUM: return Z3_OP_FPA_NUM;
            case OP_FPA_PLUS_INF: return Z3_OP_FPA_PLUS_INF;
            case OP_FPA_MINUS_INF: return Z3_OP_FPA_MINUS_INF;
            case OP_FPA_NAN: return Z3_OP_FPA_NAN;
            case OP_FPA_MINUS_ZERO: return Z3_OP_FPA_MINUS_ZERO;
            case OP_FPA_PLUS_ZERO: return Z3_OP_FPA_PLUS_ZERO;
            case OP_FPA_ADD: return Z3_OP_FPA_ADD;
            case OP_FPA_SUB: return Z3_OP_FPA_SUB;
            case OP_FPA_NEG: return Z3_OP_FPA_NEG;
            case OP_FPA_MUL: return Z3_OP_FPA_MUL;
            case OP_FPA_DIV: return Z3_OP_FPA_DIV;
            case OP_FPA_REM: return Z3_OP_FPA_REM;
            case OP_FPA_ABS: return Z3_OP_FPA_ABS;
            case OP_FPA_MIN: return Z3_OP_FPA_MIN;
            case OP_FPA_MAX: return Z3_OP_FPA_MAX;
            case OP_FPA_FMA: return Z3_OP_FPA_FMA;
            case OP_FPA_SQRT: return Z3_OP_FPA_SQRT;
            case OP_FPA_EQ: return Z3_OP_FPA_EQ;
            case OP_FPA_ROUND_TO_INTEGRAL: return Z3_OP_FPA_ROUND_TO_INTEGRAL;
            case OP_FPA_LT: return Z3_OP_FPA_LT;
            case OP_FPA_GT: return Z3_OP_FPA_GT;
            case OP_FPA_LE: return Z3_OP_FPA_LE;
            case OP_FPA_GE: return Z3_OP_FPA_GE;
            case OP_FPA_IS_NAN: return Z3_OP_FPA_IS_NAN;
            case OP_FPA_IS_INF: return Z3_OP_FPA_IS_INF;
            case OP_FPA_IS_ZERO: return Z3_OP_FPA_IS_ZERO;
            case OP_FPA_IS_NORMAL: return Z3_OP_FPA_IS_NORMAL;
            case OP_FPA_IS_SUBNORMAL: return Z3_OP_FPA_IS_SUBNORMAL;
            case OP_FPA_IS_NEGATIVE: return Z3_OP_FPA_IS_NEGATIVE;
            case OP_FPA_IS_POSITIVE: return Z3_OP_FPA_IS_POSITIVE;
            case OP_FPA_FP: return Z3_OP_FPA_FP;
            case OP_FPA_TO_FP: return Z3_OP_FPA_TO_FP;
            case OP_FPA_TO_FP_UNSIGNED: return Z3_OP_FPA_TO_FP_UNSIGNED;
            case OP_FPA_TO_UBV: return Z3_OP_FPA_TO_UBV;
            case OP_FPA_TO_SBV: return Z3_OP_FPA_TO_SBV;
            case OP_FPA_TO_REAL: return Z3_OP_FPA_TO_REAL;
            case OP_FPA_TO_IEEE_BV: return Z3_OP_FPA_TO_IEEE_BV;
            case OP_FPA_BVWRAP: return Z3_OP_FPA_BVWRAP;
            case OP_FPA_BV2RM: return Z3_OP_FPA_BV2RM;
                return Z3_OP_UNINTERPRETED;
            default:
                return Z3_OP_INTERNAL;
            }
        }

        if (mk_c(c)->m().get_label_family_id() == _d->get_family_id()) {
            switch(_d->get_decl_kind()) {
            case OP_LABEL: return Z3_OP_LABEL;
            case OP_LABEL_LIT: return Z3_OP_LABEL_LIT;
            default:
                return Z3_OP_INTERNAL;
            }
        }

        if (mk_c(c)->get_pb_fid() == _d->get_family_id()) {
            switch(_d->get_decl_kind()) {
            case OP_PB_LE: return Z3_OP_PB_LE;
            case OP_PB_GE: return Z3_OP_PB_GE;
            case OP_PB_EQ: return Z3_OP_PB_EQ;
            case OP_AT_MOST_K: return Z3_OP_PB_AT_MOST;
            case OP_AT_LEAST_K: return Z3_OP_PB_AT_LEAST;
            default: return Z3_OP_INTERNAL;
            }
        }

        return Z3_OP_UNINTERPRETED;
        Z3_CATCH_RETURN(Z3_OP_UNINTERPRETED);
    }

    unsigned Z3_API Z3_get_index_value(Z3_context c, Z3_ast a) {
        Z3_TRY;
        LOG_Z3_get_index_value(c, a);
        RESET_ERROR_CODE();
        ast* _a = reinterpret_cast<ast*>(a);
        if (!_a || _a->get_kind() != AST_VAR) {
            SET_ERROR_CODE(Z3_INVALID_ARG, nullptr);
            return 0;
        }
        var* va = to_var(_a);
        if (va) {
            return va->get_idx();
        }
        SET_ERROR_CODE(Z3_INVALID_ARG, nullptr);
        return 0;
        Z3_CATCH_RETURN(0);
    }

    Z3_ast Z3_API Z3_translate(Z3_context c, Z3_ast a, Z3_context target) {
        Z3_TRY;
        LOG_Z3_translate(c, a, target);
        RESET_ERROR_CODE();
        CHECK_VALID_AST(a, nullptr);
        if (c == target) {
            SET_ERROR_CODE(Z3_INVALID_ARG, nullptr);
            RETURN_Z3(nullptr);
        }
        SASSERT(mk_c(c)->m().contains(to_ast(a)));
        ast_translation translator(mk_c(c)->m(), mk_c(target)->m());
        ast * _result = translator(to_ast(a));
        mk_c(target)->save_ast_trail(_result);
        RETURN_Z3(of_ast(_result));
        Z3_CATCH_RETURN(nullptr);
    }

};
