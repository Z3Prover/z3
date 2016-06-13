/*++
Copyright (c) 2016 Microsoft Corporation

Module Name:

    str_rewriter.cpp

Abstract:

    AST rewriting rules for string terms.

Author:

    Murphy Berzish

Notes:

--*/

#include"str_rewriter.h"
#include"arith_decl_plugin.h"
#include"ast_pp.h"
#include"ast_util.h"
#include"well_sorted.h"

br_status str_rewriter::mk_app_core(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result) {
    SASSERT(f->get_family_id() == get_fid());

    TRACE("t_str_rw", tout << "rewrite app: " << f->get_name() << std::endl;);

    switch(f->get_decl_kind()) {
    default:
        return BR_FAILED;
    }
}

br_status str_rewriter::mk_eq_core(expr * l, expr * r, expr_ref & result) {
    // from seq_rewriter
    expr_ref_vector lhs(m()), rhs(m()), res(m());
    bool changed = false;
    if (!reduce_eq(l, r, lhs, rhs, changed)) {
        result = m().mk_false();
        return BR_DONE;
    }
    if (!changed) {
        return BR_FAILED;
    }
    for (unsigned i = 0; i < lhs.size(); ++i) {
        res.push_back(m().mk_eq(lhs[i].get(), rhs[i].get()));
    }
    result = mk_and(res);
    return BR_REWRITE3;
}

bool str_rewriter::reduce_eq(expr * l, expr * r, expr_ref_vector & lhs, expr_ref_vector & rhs, bool & change) {
    // TODO inspect seq_rewriter::reduce_eq()
    change = false;
    return true;
}

bool str_rewriter::reduce_eq(expr_ref_vector& ls, expr_ref_vector& rs, expr_ref_vector& lhs, expr_ref_vector& rhs, bool& change) {
    // TODO inspect seq_rewriter::reduce_eq()
    change = false;
    return true;
}

