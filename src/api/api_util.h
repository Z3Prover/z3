/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    api_util.h

Abstract:
    Goodies used to build the Z3 external API.

Author:

    Leonardo de Moura (leonardo) 2012-02-29.

Revision History:

--*/
#pragma once

#include "util/params.h"
#include "util/lbool.h"
#include "ast/ast.h"

#define Z3_TRY try {
#define Z3_CATCH_CORE(CODE) } catch (z3_exception & ex) { mk_c(c)->handle_exception(ex); CODE }
#define Z3_CATCH Z3_CATCH_CORE(return;)
#define Z3_CATCH_RETURN(VAL) Z3_CATCH_CORE(return VAL;)
#define Z3_CATCH_RETURN_NO_HANDLE(VAL) } catch (z3_exception &) { return VAL; }

#define CHECK_REF_COUNT(a) (reinterpret_cast<ast const*>(a)->get_ref_count() > 0)

namespace api {
    class context;

    // Generic wrapper for ref-count objects exposed by the API
    class object {
        unsigned m_ref_count;
        unsigned m_id;
        context& m_context;
    public:
        object(context& c);
        virtual ~object() {}
        unsigned ref_count() const { return m_ref_count; }
        unsigned id() const { return m_id; }
        void inc_ref();
        void dec_ref();
    };
};

inline ast * to_ast(Z3_ast a) { return reinterpret_cast<ast *>(a); }
inline Z3_ast of_ast(ast* a) { return reinterpret_cast<Z3_ast>(a); }

inline expr * to_expr(Z3_ast a) { return reinterpret_cast<expr*>(a); }
inline Z3_ast of_expr(expr* e) { return reinterpret_cast<Z3_ast>(e); }

inline expr * const * to_exprs(unsigned n, Z3_ast const* a) { return reinterpret_cast<expr* const*>(a); }
inline Z3_ast * const * of_exprs(expr* const* e) { return reinterpret_cast<Z3_ast* const*>(e); }

inline app * to_app(Z3_app a) { return reinterpret_cast<app*>(a); }
inline app * to_app(Z3_ast a) { return reinterpret_cast<app*>(a); }
inline Z3_app of_app(app* a) { return reinterpret_cast<Z3_app>(a); }

inline app * const* to_apps(Z3_ast const* a) { return reinterpret_cast<app * const*>(a); }

inline ast * const * to_asts(Z3_ast const* a) { return reinterpret_cast<ast* const*>(a); }

inline sort * to_sort(Z3_sort a) { return reinterpret_cast<sort*>(a); }
inline Z3_sort of_sort(sort* s) { return reinterpret_cast<Z3_sort>(s); }

inline sort * const *  to_sorts(Z3_sort const* a) { return reinterpret_cast<sort* const*>(a); }
inline Z3_sort const * of_sorts(sort* const* s) { return reinterpret_cast<Z3_sort const*>(s); }

inline func_decl * to_func_decl(Z3_func_decl a) { return reinterpret_cast<func_decl*>(a); }
inline Z3_func_decl of_func_decl(func_decl* f) { return reinterpret_cast<Z3_func_decl>(f); }

inline func_decl * const * to_func_decls(Z3_func_decl const* f) { return reinterpret_cast<func_decl*const*>(f); }

inline symbol to_symbol(Z3_symbol s) { return symbol::c_api_ext2symbol(s); }
inline Z3_symbol of_symbol(symbol s) { return static_cast<Z3_symbol>(s.c_api_symbol2ext()); }

inline Z3_pattern of_pattern(ast* a) { return reinterpret_cast<Z3_pattern>(a); }
inline app* to_pattern(Z3_pattern p) { return reinterpret_cast<app*>(p); }

inline Z3_lbool of_lbool(lbool b) { return static_cast<Z3_lbool>(b); }
inline lbool    to_lbool(Z3_lbool b) { return static_cast<lbool>(b); }

struct Z3_params_ref : public api::object {
    params_ref m_params;
    Z3_params_ref(api::context& c): api::object(c) {}
    ~Z3_params_ref() override {}
};

inline Z3_params_ref * to_params(Z3_params p) { return reinterpret_cast<Z3_params_ref *>(p); }
inline Z3_params of_params(Z3_params_ref * p) { return reinterpret_cast<Z3_params>(p); }
inline params_ref& to_param_ref(Z3_params p) { return p == nullptr ? const_cast<params_ref&>(params_ref::get_empty()) : to_params(p)->m_params; }

struct Z3_param_descrs_ref : public api::object {
    param_descrs m_descrs;
    Z3_param_descrs_ref(api::context& c): api::object(c) {}
    ~Z3_param_descrs_ref() override {}
};

inline Z3_param_descrs_ref * to_param_descrs(Z3_param_descrs p) { return reinterpret_cast<Z3_param_descrs_ref *>(p); }
inline Z3_param_descrs of_param_descrs(Z3_param_descrs_ref * p) { return reinterpret_cast<Z3_param_descrs>(p); }
inline param_descrs * to_param_descrs_ptr(Z3_param_descrs p) { return p == nullptr ? nullptr : &(to_param_descrs(p)->m_descrs); }


#define SKIP ((void) 0)

#define MK_UNARY_BODY(NAME, FID, OP, EXTRA_CODE)                \
    Z3_TRY;                                                     \
    RESET_ERROR_CODE();                                         \
    EXTRA_CODE;                                                 \
    expr * _n = to_expr(n);                                     \
    ast* a = mk_c(c)->m().mk_app(FID, OP, 0, 0, 1, &_n);        \
    mk_c(c)->save_ast_trail(a);                                 \
    check_sorts(c, a);                                          \
    RETURN_Z3(of_ast(a));                                       \
    Z3_CATCH_RETURN(0);

#define MK_UNARY(NAME, FID, OP, EXTRA_CODE)     \
Z3_ast Z3_API NAME(Z3_context c, Z3_ast n) {    \
    LOG_ ## NAME(c, n);                         \
    MK_UNARY_BODY(NAME, FID, OP, EXTRA_CODE);   \
}

#define MK_BINARY_BODY(NAME, FID, OP, EXTRA_CODE)               \
    Z3_TRY;                                                     \
    RESET_ERROR_CODE();                                         \
    EXTRA_CODE;                                                 \
    expr * args[2] = { to_expr(n1), to_expr(n2) };              \
    ast* a = mk_c(c)->m().mk_app(FID, OP, 0, 0, 2, args);       \
    mk_c(c)->save_ast_trail(a);                                 \
    check_sorts(c, a);                                          \
    RETURN_Z3(of_ast(a));                                       \
    Z3_CATCH_RETURN(0);
 
#define MK_BINARY(NAME, FID, OP, EXTRA_CODE)                    \
Z3_ast Z3_API NAME(Z3_context c, Z3_ast n1, Z3_ast n2) {        \
    LOG_ ## NAME(c, n1, n2);                                    \
    MK_BINARY_BODY(NAME, FID, OP, EXTRA_CODE);                  \
}

#define MK_TERNARY_BODY(NAME, FID, OP, EXTRA_CODE)               \
    Z3_TRY;                                                     \
    RESET_ERROR_CODE();                                         \
    EXTRA_CODE;                                                 \
    expr * args[3] = { to_expr(n1), to_expr(n2), to_expr(n3) }; \
    ast* a = mk_c(c)->m().mk_app(FID, OP, 0, 0, 3, args);       \
    mk_c(c)->save_ast_trail(a);                                 \
    check_sorts(c, a);                                          \
    RETURN_Z3(of_ast(a));                                       \
    Z3_CATCH_RETURN(0);
 
#define MK_TERNARY(NAME, FID, OP, EXTRA_CODE)                            \
    Z3_ast Z3_API NAME(Z3_context c, Z3_ast n1, Z3_ast n2, Z3_ast n3) { \
    LOG_ ## NAME(c, n1, n2, n3);                                        \
    MK_TERNARY_BODY(NAME, FID, OP, EXTRA_CODE);                          \
}

#define MK_NARY(NAME, FID, OP, EXTRA_CODE)                              \
Z3_ast Z3_API NAME(Z3_context c, unsigned num_args, Z3_ast const* args) { \
    Z3_TRY;                                                             \
    LOG_ ## NAME(c, num_args, args);                                    \
    RESET_ERROR_CODE();                                                 \
    EXTRA_CODE;                                                         \
    ast* a = mk_c(c)->m().mk_app(FID, OP, 0, 0, num_args, to_exprs(num_args, args)); \
    mk_c(c)->save_ast_trail(a);                                         \
    check_sorts(c, a);                                                  \
    RETURN_Z3(of_ast(a));                                               \
    Z3_CATCH_RETURN(0);                                                 \
}

