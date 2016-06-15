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
        // TODO if we ever figure out how to assert axioms in here, add the axiom code from Z3str2's strAstReduce.cpp
        return BR_FAILED;
    }
}

br_status str_rewriter::mk_str_StartsWith(expr * haystack, expr * needle, expr_ref & result) {
    TRACE("t_str_rw", tout << "rewrite (StartsWith " << mk_pp(haystack, m()) << " " << mk_pp(needle, m()) << ")" << std::endl;);
    if (m_strutil.is_string(haystack) && m_strutil.is_string(needle)) {
        TRACE("t_str_rw", tout << "evaluating constant StartsWith predicate" << std::endl;);
        std::string haystackStr = m_strutil.get_string_constant_value(haystack);
        std::string needleStr = m_strutil.get_string_constant_value(needle);
        if (haystackStr.length() < needleStr.length()) {
            result = m().mk_false();
            return BR_DONE;
        } else {
            if (haystackStr.substr(0, needleStr.length()) == needleStr) {
                result = m().mk_true();
            } else {
                result = m().mk_false();
            }
            return BR_DONE;
        }
    } else {
        return BR_FAILED;
    }
}

br_status str_rewriter::mk_str_EndsWith(expr * haystack, expr * needle, expr_ref & result) {
    TRACE("t_str_rw", tout << "rewrite (EndsWith " << mk_pp(haystack, m()) << " " << mk_pp(needle, m()) << ")" << std::endl;);
    if (m_strutil.is_string(haystack) && m_strutil.is_string(needle)) {
        TRACE("t_str_rw", tout << "evaluating constant EndsWith predicate" << std::endl;);
        std::string haystackStr = m_strutil.get_string_constant_value(haystack);
        std::string needleStr = m_strutil.get_string_constant_value(needle);
        if (haystackStr.length() < needleStr.length()) {
            result = m().mk_false();
            return BR_DONE;
        } else {
            if (haystackStr.substr(haystackStr.length() - needleStr.length(), needleStr.length()) == needleStr) {
                result = m().mk_true();
            } else {
                result = m().mk_false();
            }
            return BR_DONE;
        }
    } else {
        return BR_FAILED;
    }
}

br_status str_rewriter::mk_str_Contains(expr * haystack, expr * needle, expr_ref & result) {
    TRACE("t_str_rw", tout << "rewrite (Contains " << mk_pp(haystack, m()) << " " << mk_pp(needle, m()) << ")" << std::endl;);
    if (haystack == needle) {
        TRACE("t_str_rw", tout << "eliminate (Contains) over identical terms" << std::endl;);
        result = m().mk_true();
        return BR_DONE;
    } else if (m_strutil.is_string(haystack) && m_strutil.is_string(needle)) {
        TRACE("t_str_rw", tout << "evaluating constant Contains predicate" << std::endl;);
        std::string haystackStr = m_strutil.get_string_constant_value(haystack);
        std::string needleStr = m_strutil.get_string_constant_value(needle);
        if (haystackStr.find(needleStr) != std::string::npos) {
            result = m().mk_true();
        } else {
            result = m().mk_false();
        }
        return BR_DONE;
    } else {
        return BR_FAILED;
    }
}

br_status str_rewriter::mk_str_Indexof(expr * haystack, expr * needle, expr_ref & result) {
    TRACE("t_str_rw", tout << "rewrite (Indexof " << mk_pp(haystack, m()) << " " << mk_pp(needle, m()) << ")" << std::endl;);
    if (m_strutil.is_string(haystack) && m_strutil.is_string(needle)) {
        TRACE("t_str_rw", tout << "evaluating constant Indexof expression" << std::endl;);
        std::string haystackStr = m_strutil.get_string_constant_value(haystack);
        std::string needleStr = m_strutil.get_string_constant_value(needle);
        if (haystackStr.find(needleStr) != std::string::npos) {
            int index = haystackStr.find(needleStr);
            result = m_autil.mk_numeral(rational(index), true);
        } else {
            result = m_autil.mk_numeral(rational(-1), true);
        }
        return BR_DONE;
    } else {
        return BR_FAILED;
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
    case OP_STR_STARTSWITH:
        SASSERT(num_args == 2);
        return mk_str_StartsWith(args[0], args[1], result);
    case OP_STR_ENDSWITH:
        SASSERT(num_args == 2);
        return mk_str_EndsWith(args[0], args[1], result);
    case OP_STR_CONTAINS:
        SASSERT(num_args == 2);
        return mk_str_Contains(args[0], args[1], result);
    case OP_STR_INDEXOF:
        SASSERT(num_args == 2);
        return mk_str_Indexof(args[0], args[1], result);
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

