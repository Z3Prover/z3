/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    cmd_util.cpp

Abstract:
    Macros for defining new SMT2 front-end cmds.

Author:

    Leonardo (leonardo) 2011-04-01

Notes:

--*/
#include "cmd_context/cmd_context.h"

ast * get_ast_ref(cmd_context & ctx, symbol const & v) {
    object_ref * r = ctx.find_object_ref(v);
    SASSERT(r != 0);
    if (r->kind() != ast_object_ref::cls_kind()) 
        throw cmd_exception("global variable does not reference an AST");
    return static_cast<ast_object_ref*>(r)->get_ast();
}

expr * get_expr_ref(cmd_context & ctx, symbol const & v) {
    ast * r = get_ast_ref(ctx, v);
    if (!is_expr(r))
        throw cmd_exception("global variable does not reference a term");
    return to_expr(r);
}

void store_expr_ref(cmd_context & ctx, symbol const & v, expr * t) {
    ctx.insert(v, alloc(ast_object_ref, ctx, t));
}

