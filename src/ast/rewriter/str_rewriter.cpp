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

br_status str_rewriter::mk_str_Indexof2(expr * arg0, expr * arg1, expr * arg2, expr_ref & result) {
    TRACE("t_str_rw", tout << "rewrite (Indexof2 " << mk_pp(arg0, m()) << " " << mk_pp(arg1, m()) << " " << mk_pp(arg2, m()) << ")" << std::endl;);
    //if (getNodeType(t, args[0]) == my_Z3_ConstStr && getNodeType(t, args[1]) == my_Z3_ConstStr && getNodeType(t, args[2]) == my_Z3_Num) {
    rational arg2Int;
    if (m_strutil.is_string(arg0) && m_strutil.is_string(arg1) && m_autil.is_numeral(arg2, arg2Int)) {
        TRACE("t_str_rw", tout << "evaluating constant Indexof2 expression" << std::endl;);
        std::string arg0str = m_strutil.get_string_constant_value(arg0);
        std::string arg1str = m_strutil.get_string_constant_value(arg1);
        if (arg2Int >= rational((unsigned)arg0str.length())) {
            result = m_autil.mk_numeral(rational(-1), true);
        } else if (arg2Int < rational(0)) {
            int index = arg0str.find(arg1str);
            result = m_autil.mk_numeral(rational(index), true);
        } else {
            std::string suffixStr = arg0str.substr(arg2Int.get_unsigned(), arg0str.length() - arg2Int.get_unsigned());
            if (suffixStr.find(arg1str) != std::string::npos) {
                int index = suffixStr.find(arg1str) + arg2Int.get_unsigned();
                result = m_autil.mk_numeral(rational(index), true);
            } else {
                result = m_autil.mk_numeral(rational(-1), true);
            }
        }
        return BR_DONE;
    } else {
        return BR_FAILED;
    }
}

br_status str_rewriter::mk_str_LastIndexof(expr * haystack, expr * needle, expr_ref & result) {
    TRACE("t_str_rw", tout << "rewrite (LastIndexof " << mk_pp(haystack, m()) << " " << mk_pp(needle, m()) << ")" << std::endl;);
    if (m_strutil.is_string(haystack) && m_strutil.is_string(needle)) {
        TRACE("t_str_rw", tout << "evaluating constant LastIndexof expression" << std::endl;);
        std::string arg0Str = m_strutil.get_string_constant_value(haystack);
        std::string arg1Str = m_strutil.get_string_constant_value(needle);
        if (arg0Str.rfind(arg1Str) != std::string::npos) {
            int index = arg0Str.rfind(arg1Str);
            result = m_autil.mk_numeral(rational(index), true);
        } else {
            result = m_autil.mk_numeral(rational(-1), true);
        }
        return BR_DONE;
    } else {
        return BR_FAILED;
    }
}

br_status str_rewriter::mk_str_Replace(expr * base, expr * source, expr * target, expr_ref & result) {
    TRACE("t_str_rw", tout << "rewrite (Replace " << mk_pp(base, m()) << " " << mk_pp(source, m()) << " " << mk_pp(target, m()) << ")" << std::endl;);
    if (m_strutil.is_string(base) && m_strutil.is_string(source) && m_strutil.is_string(target)) {
        std::string arg0Str = m_strutil.get_string_constant_value(base);
        std::string arg1Str = m_strutil.get_string_constant_value(source);
        std::string arg2Str = m_strutil.get_string_constant_value(target);
        if (arg0Str.find(arg1Str) != std::string::npos) {
            int index1 = arg0Str.find(arg1Str);
            int index2 = index1 + arg1Str.length();
            std::string substr0 = arg0Str.substr(0, index1);
            std::string substr2 = arg0Str.substr(index2);
            std::string replaced = substr0 + arg2Str + substr2;
            result = m_strutil.mk_string(replaced);
        } else {
            result = base;
        }
        return BR_DONE;
    } else {
        return BR_FAILED;
    }
}

br_status str_rewriter::mk_re_Str2Reg(expr * str, expr_ref & result) {
	// the argument to Str2Reg *must* be a string constant
	// TODO is an assertion error too strict here? this basically crashes the solver
	VERIFY(m_strutil.is_string(str));
	return BR_FAILED;
}

br_status str_rewriter::mk_re_RegexIn(expr * str, expr * re, expr_ref & result) {
	// fast path:
	// (RegexIn E (Str2Reg S)) --> (= E S)
	if (m_strutil.is_re_Str2Reg(re)) {
		TRACE("t_str_rw", tout << "RegexIn fast path: " << mk_pp(str, m()) << " in " << mk_pp(re, m()) << std::endl;);
		expr * regexStr = to_app(re)->get_arg(0);
		VERIFY(m_strutil.is_string(regexStr));
		result = m().mk_eq(str, regexStr);
		return BR_REWRITE_FULL;
	}

	return BR_FAILED;
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
    case OP_STR_INDEXOF2:
        SASSERT(num_args == 3);
        return mk_str_Indexof2(args[0], args[1], args[2], result);
    case OP_STR_LASTINDEXOF:
        SASSERT(num_args == 2);
        return mk_str_LastIndexof(args[0], args[1], result);
    case OP_STR_REPLACE:
        SASSERT(num_args == 3);
        return mk_str_Replace(args[0], args[1], args[2], result);
    case OP_RE_STR2REGEX:
    	SASSERT(num_args == 1);
    	return mk_re_Str2Reg(args[0], result);
    case OP_RE_REGEXIN:
    	SASSERT(num_args == 2);
    	return mk_re_RegexIn(args[0], args[1], result);
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

