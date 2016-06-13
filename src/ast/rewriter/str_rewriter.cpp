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

br_status str_rewriter::mk_str_CharAt(expr * arg0, expr * arg1, expr_ref & result) {
    TRACE("t_str_rw", tout << "rewrite (CharAt " << mk_pp(arg0, m()) << " " << mk_pp(arg1, m()) << ")" << std::endl;);
    // if arg0 is a string constant and arg1 is an integer constant,
    // we can rewrite this by evaluating the expression
    rational arg1Int;
    if (m_strutil.is_string(arg0) && m_autil.is_numeral(arg1, arg1Int)) {
        TRACE("t_str_rw", tout << "evaluating constant CharAt expression" << std::endl;);
        std::string arg0Str = m_strutil.get_string_constant_value(arg0);
        std::string resultStr;
        if (arg1Int >= rational(0) && arg1Int <= rational((unsigned)arg0Str.length())) {
            resultStr = arg0Str.at(arg1Int.get_unsigned());
            TRACE("t_str_rw", tout << "result is '" << resultStr << "'" << std::endl;);
        } else {
            resultStr = "";
            TRACE("t_str_rw", tout << "bogus length argument, result is empty string" << std::endl;);
        }
        result = m_strutil.mk_string(resultStr);
        return BR_DONE;
    } else {
        // TODO NEXT
        NOT_IMPLEMENTED_YET();
        /*
        Z3_ast ts0 = my_mk_internal_string_var(t);
        Z3_ast ts1 = my_mk_internal_string_var(t);
        Z3_ast ts2 = my_mk_internal_string_var(t);

        Z3_ast cond = mk_2_and(t, Z3_mk_ge(ctx, args[1], mk_int(ctx, 0)), Z3_mk_lt(ctx, args[1], mk_length(t, args[0])));

        Z3_ast and_item[3];
        and_item[0] = Z3_mk_eq(ctx, args[0], mk_concat(t, ts0, mk_concat(t, ts1, ts2)));
        and_item[1] = Z3_mk_eq(ctx, args[1], mk_length(t, ts0));
        and_item[2] = Z3_mk_eq(ctx, mk_length(t, ts1), mk_int(ctx, 1));
        Z3_ast thenBranch = Z3_mk_and(ctx, 3, and_item);
        Z3_ast elseBranch = Z3_mk_eq(ctx, ts1, my_mk_str_value(t, ""));
        breakdownAssert = Z3_mk_ite(ctx, cond, thenBranch, elseBranch);
        return ts1;
        */
    }
}

br_status str_rewriter::mk_app_core(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result) {
    SASSERT(f->get_family_id() == get_fid());

    TRACE("t_str_rw", tout << "rewrite app: " << f->get_name() << std::endl;);

    // TODO more rewrites for really easy cases, e.g. (Concat "abc" "def")...
    switch(f->get_decl_kind()) {
    case OP_STR_CHARAT:
        SASSERT(num_args == 2);
        return mk_str_CharAt(args[0], args[1], result);
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

