/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    char_rewriter.h

Abstract:

    Basic rewriting rules for characters constraints.

Author:

    Nikolaj Bjorner (nbjorner) 2022-03-10

Notes:

--*/
#pragma once

#include "ast/char_decl_plugin.h"
#include "ast/rewriter/rewriter_types.h"
#include "util/params.h"
#include "util/lbool.h"


/**
   \brief Cheap rewrite rules for character constraints
*/
class char_rewriter {
    ast_manager& m;
    char_decl_plugin* m_char;

    br_status mk_char_from_bv(expr* e, expr_ref& result);

    br_status mk_char_to_int(expr* e, expr_ref& result);

    br_status mk_char_le(expr* a, expr* b, expr_ref& result);

    br_status mk_char_is_digit(expr* a, expr_ref& result);

    br_status mk_char_to_bv(expr* a, expr_ref& result);

public:

    char_rewriter(ast_manager& m);

    family_id get_fid();

    br_status mk_app_core(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result);

    expr_ref mk_app(func_decl* f, expr_ref_vector const& args) { return mk_app(f, args.size(), args.data()); }

    expr_ref mk_app(func_decl* f, unsigned n, expr* const* args) { 
        expr_ref result(m);
        if (f->get_family_id() != get_fid() ||
            BR_FAILED == mk_app_core(f, n, args, result))
            result = m.mk_app(f, n, args);
        return result;
    }

};

