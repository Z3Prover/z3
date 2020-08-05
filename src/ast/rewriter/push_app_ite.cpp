/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    push_app_ite.cpp

Abstract:

    TODO: Write a better ite lifter


Author:

    Leonardo de Moura (leonardo) 2008-05-14.

Revision History:

--*/
#include "ast/rewriter/push_app_ite.h"
#include "ast/ast_pp.h"


static int has_ite_arg(ast_manager& m, unsigned num_args, expr * const * args) {
    for (unsigned i = 0; i < num_args; i++)
        if (m.is_ite(args[i]))
            return i;
    return -1;
}


/**
   \brief Default (conservative) implementation. Return true if there one and only one ite-term argument.
*/
bool push_app_ite_cfg::is_target(func_decl * decl, unsigned num_args, expr * const * args) {
    if (m.is_ite(decl))
        return false;
    bool found_ite = false;
    for (unsigned i = 0; i < num_args; i++) {
        if (m.is_ite(args[i]) && !m.is_bool(args[i])) {
            if (found_ite) {
                if (m_conservative)
                    return false;
            }
            else {
                found_ite = true;
            }
        }
    }
    CTRACE("push_app_ite", found_ite, tout << "found target for push app ite:\n";
           tout << "conservative " << m_conservative << "\n";
           tout << decl->get_name();
           for (unsigned i = 0; i < num_args; i++) tout << " " << mk_pp(args[i], m);
           tout << "\n";);
    return found_ite;
}

br_status push_app_ite_cfg::reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
    if (!is_target(f, num, args)) {
        return BR_FAILED;
    }
    int ite_arg_idx = has_ite_arg(m, num, args);
    if (ite_arg_idx < 0) {
        return BR_FAILED;
    }
    app * ite               = to_app(args[ite_arg_idx]);
    expr * c = nullptr, * t = nullptr, * e = nullptr;
    VERIFY(m.is_ite(ite, c, t, e));
    expr ** args_prime      = const_cast<expr**>(args);
    expr * old              = args_prime[ite_arg_idx];
    args_prime[ite_arg_idx] = t;
    expr_ref t_new(m.mk_app(f, num, args_prime), m);
    args_prime[ite_arg_idx] = e;
    expr_ref e_new(m.mk_app(f, num, args_prime), m);
    args_prime[ite_arg_idx] = old;
    result = m.mk_ite(c, t_new, e_new);
    TRACE("push_app_ite", tout << result << "\n";);
    if (m.proofs_enabled()) {
        result_pr = m.mk_rewrite(m.mk_app(f, num, args), result);
    }
    return BR_REWRITE2;
}

bool ng_push_app_ite_cfg::is_target(func_decl * decl, unsigned num_args, expr * const * args) {
    bool r = push_app_ite_cfg::is_target(decl, num_args, args);
    if (!r) 
        return false;
    for (unsigned i = 0; i < num_args; i++)
        if (!is_ground(args[i]))
            return true;
    return false;
}
