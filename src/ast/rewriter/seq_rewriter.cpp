/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    seq_rewriter.cpp

Abstract:

    Basic rewriting rules for sequences constraints.

Author:

    Nikolaj Bjorner (nbjorner) 2015-12-5

Notes:

--*/

#include"seq_rewriter.h"
#include"arith_decl_plugin.h"


br_status seq_rewriter::mk_app_core(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result) {
    SASSERT(f->get_family_id() == get_fid());
    
    switch(f->get_decl_kind()) {

    case OP_SEQ_UNIT:
    case OP_SEQ_EMPTY:
    case OP_SEQ_CONCAT:
    case OP_SEQ_CONS:
    case OP_SEQ_REV_CONS:
    case OP_SEQ_HEAD:
    case OP_SEQ_TAIL:
    case OP_SEQ_LAST:
    case OP_SEQ_FIRST:
    case OP_SEQ_PREFIX_OF:
    case OP_SEQ_SUFFIX_OF:
    case OP_SEQ_SUBSEQ_OF:
    case OP_SEQ_EXTRACT:
    case OP_SEQ_NTH:
    case OP_SEQ_LENGTH:

    case OP_RE_PLUS:
    case OP_RE_STAR:
    case OP_RE_OPTION:
    case OP_RE_RANGE:
    case OP_RE_CONCAT:
    case OP_RE_UNION:
    case OP_RE_INTERSECT:
    case OP_RE_COMPLEMENT:
    case OP_RE_DIFFERENCE:
    case OP_RE_LOOP:
    case OP_RE_EMPTY_SET:
    case OP_RE_FULL_SET:
    case OP_RE_EMPTY_SEQ:
    case OP_RE_OF_SEQ:
    case OP_RE_OF_PRED:
    case OP_RE_MEMBER:
        return BR_FAILED;

    // string specific operators.
    case OP_STRING_CONST:
        return BR_FAILED;
    case OP_STRING_CONCAT: 
        SASSERT(num_args == 2);
        return mk_str_concat(args[0], args[1], result);
    case OP_STRING_LENGTH:
        SASSERT(num_args == 1);
        return mk_str_length(args[0], result);
    case OP_STRING_SUBSTR: 
        SASSERT(num_args == 3);
        return mk_str_substr(args[0], args[1], args[2], result);
    case OP_STRING_STRCTN: 
        SASSERT(num_args == 2);
        return mk_str_strctn(args[0], args[1], result);
    case OP_STRING_CHARAT:
        SASSERT(num_args == 2);
        return mk_str_charat(args[0], args[1], result); 
    case OP_STRING_STRIDOF: 
        SASSERT(num_args == 2);
        return mk_str_stridof(args[0], args[1], result);
    case OP_STRING_STRREPL: 
        SASSERT(num_args == 3);
        return mk_str_strrepl(args[0], args[1], args[2], result);
    case OP_STRING_PREFIX: 
        SASSERT(num_args == 2);
        return mk_str_prefix(args[0], args[1], result);
    case OP_STRING_SUFFIX: 
        SASSERT(num_args == 2);
        return mk_str_suffix(args[0], args[1], result);
    case OP_STRING_ITOS: 
        SASSERT(num_args == 1);
        return mk_str_itos(args[0], result);
    case OP_STRING_STOI: 
        SASSERT(num_args == 1);
        return mk_str_stoi(args[0], result);
    //case OP_STRING_U16TOS: 
    //case OP_STRING_STOU16: 
    //case OP_STRING_U32TOS: 
    //case OP_STRING_STOU32: 
    case OP_STRING_IN_REGEXP: 
    case OP_STRING_TO_REGEXP: 
    case OP_REGEXP_CONCAT: 
    case OP_REGEXP_UNION: 
    case OP_REGEXP_INTER: 
    case OP_REGEXP_STAR: 
    case OP_REGEXP_PLUS: 
    case OP_REGEXP_OPT: 
    case OP_REGEXP_RANGE: 
    case OP_REGEXP_LOOP: 
        return BR_FAILED;
    }
    return BR_FAILED;
}

br_status seq_rewriter::mk_str_concat(expr* a, expr* b, expr_ref& result) {
    std::string c, d;
    if (m_util.str.is_const(a, c) && m_util.str.is_const(b, d)) {
        result = m_util.str.mk_string(c + d);
        return BR_DONE;
    }
    return BR_FAILED;
}
br_status seq_rewriter::mk_str_length(expr* a, expr_ref& result) {
    std::string b;
    if (m_util.str.is_const(a, b)) {
        result = arith_util(m()).mk_numeral(rational(b.length()), true);
    }
    return BR_FAILED;
}
br_status seq_rewriter::mk_str_substr(expr* a, expr* b, expr* c, expr_ref& result) {
    return BR_FAILED;
}
br_status seq_rewriter::mk_str_strctn(expr* a, expr* b, expr_ref& result) {
    std::string c, d;
    if (m_util.str.is_const(a, c) && m_util.str.is_const(b, d)) {
        result = m().mk_bool_val(0 != strstr(d.c_str(), c.c_str()));
        return BR_DONE;
    }
    return BR_FAILED;
}
br_status seq_rewriter::mk_str_charat(expr* a, expr* b, expr_ref& result) {
    return BR_FAILED;
}
br_status seq_rewriter::mk_str_stridof(expr* a, expr* b, expr_ref& result) {
    return BR_FAILED;
}
br_status seq_rewriter::mk_str_strrepl(expr* a, expr* b, expr* c, expr_ref& result) {
    return BR_FAILED;
}
br_status seq_rewriter::mk_str_prefix(expr* a, expr* b, expr_ref& result) {
    std::string s1, s2;
    if (m_util.str.is_const(a, s1) && m_util.str.is_const(b, s2)) {
        bool prefix = s1.length() <= s2.length();
        for (unsigned i = 0; i < s1.length() && prefix; ++i) {
            prefix = s1[i] == s2[i];
        }
        result = m().mk_bool_val(prefix);
        return BR_DONE;
    }
    return BR_FAILED;
}
br_status seq_rewriter::mk_str_suffix(expr* a, expr* b, expr_ref& result) {
    std::string s1, s2;
    if (m_util.str.is_const(a, s1) && m_util.str.is_const(b, s2)) {
        bool suffix = s1.length() <= s2.length();
        for (unsigned i = 0; i < s1.length() && suffix; ++i) {
            suffix = s1[s1.length() - i - 1] == s2[s2.length() - i - 1];
        }
        result = m().mk_bool_val(suffix);
        return BR_DONE;
    }
    return BR_FAILED;
}
br_status seq_rewriter::mk_str_itos(expr* a, expr_ref& result) {
    arith_util autil(m());
    rational r;
    if (autil.is_numeral(a, r)) {
        result = m_util.str.mk_string(r.to_string());
        return BR_DONE;
    }
    return BR_FAILED;
}
br_status seq_rewriter::mk_str_stoi(expr* a, expr_ref& result) {
    arith_util autil(m());
    std::string s;
    if (m_util.str.is_const(a, s)) {
        
    }
    return BR_FAILED;
}
br_status seq_rewriter::mk_str_in_regexp(expr* a, expr* b, expr_ref& result) {
    return BR_FAILED;
}
br_status seq_rewriter::mk_str_to_regexp(expr* a, expr_ref& result) {
    return BR_FAILED;
}
br_status seq_rewriter::mk_re_concat(expr* a, expr* b, expr_ref& result) {
    return BR_FAILED;
}
br_status seq_rewriter::mk_re_union(expr* a, expr* b, expr_ref& result) {
    return BR_FAILED;
}
br_status seq_rewriter::mk_re_star(expr* a, expr_ref& result) {
    return BR_FAILED;
}
br_status seq_rewriter::mk_re_plus(expr* a, expr_ref& result) {
    return BR_FAILED;
}
br_status seq_rewriter::mk_re_opt(expr* a, expr_ref& result) {
    return BR_FAILED;
}
