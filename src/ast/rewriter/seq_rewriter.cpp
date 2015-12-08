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
#include"ast_pp.h"


br_status seq_rewriter::mk_app_core(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result) {
    SASSERT(f->get_family_id() == get_fid());
    
    switch(f->get_decl_kind()) {

    case OP_SEQ_UNIT:
    case OP_SEQ_EMPTY:

    case OP_RE_PLUS:
    case OP_RE_STAR:
    case OP_RE_OPTION:
    case OP_RE_RANGE:
    case OP_RE_CONCAT:
    case OP_RE_UNION:
    case OP_RE_INTERSECT:
    case OP_RE_LOOP:
    case OP_RE_EMPTY_SET:
    case OP_RE_FULL_SET:
    case OP_RE_OF_PRED:
        return BR_FAILED;
    
    case OP_SEQ_CONCAT: 
        SASSERT(num_args == 2);
        return mk_seq_concat(args[0], args[1], result);
    case OP_SEQ_LENGTH:
        SASSERT(num_args == 1);
        return mk_str_length(args[0], result);
    case OP_SEQ_EXTRACT:
        SASSERT(num_args == 3);
        return mk_str_substr(args[0], args[1], args[2], result);
    case OP_SEQ_CONTAINS: 
        SASSERT(num_args == 2);
        return mk_str_strctn(args[0], args[1], result);
    case OP_SEQ_AT:
        SASSERT(num_args == 2);
        return mk_str_at(args[0], args[1], result); 
    case OP_SEQ_PREFIX: 
        SASSERT(num_args == 2);
        return mk_seq_prefix(args[0], args[1], result);
    case OP_SEQ_SUFFIX: 
        SASSERT(num_args == 2);
        return mk_seq_suffix(args[0], args[1], result);
    case OP_SEQ_TO_RE:
        return BR_FAILED;
    case OP_SEQ_IN_RE:
        return BR_FAILED;

    case OP_STRING_CONST:
        return BR_FAILED;
    case OP_STRING_STRIDOF: 
        SASSERT(num_args == 3);
        return mk_str_stridof(args[0], args[1], args[2], result);
    case OP_STRING_STRREPL: 
        SASSERT(num_args == 3);
        return mk_str_strrepl(args[0], args[1], args[2], result);
    case OP_STRING_ITOS: 
        SASSERT(num_args == 1);
        return mk_str_itos(args[0], result);
    case OP_STRING_STOI: 
        SASSERT(num_args == 1);
        return mk_str_stoi(args[0], result);
    case OP_REGEXP_LOOP: 
        return BR_FAILED;
    case _OP_STRING_CONCAT:
    case _OP_STRING_PREFIX:
    case _OP_STRING_SUFFIX:
    case _OP_STRING_STRCTN:
    case _OP_STRING_LENGTH:
    case _OP_STRING_CHARAT:
    case _OP_STRING_IN_REGEXP: 
    case _OP_STRING_TO_REGEXP: 
    case _OP_STRING_SUBSTR: 

        UNREACHABLE();
    }
    return BR_FAILED;
}

/*
   string + string = string
   a + (b + c) = (a + b) + c
   a + "" = a
   "" + a = a
   (a + string) + string = a + string
*/
br_status seq_rewriter::mk_seq_concat(expr* a, expr* b, expr_ref& result) {
    std::string s1, s2;
    expr* c, *d;
    bool isc1 = m_util.str.is_string(a, s1);
    bool isc2 = m_util.str.is_string(b, s2);
    if (isc1 && isc2) {
        result = m_util.str.mk_string(s1 + s2);
        return BR_DONE;
    }
    if (m_util.str.is_concat(b, c, d)) {
        result = m_util.str.mk_concat(m_util.str.mk_concat(a, c), d);
        return BR_REWRITE2;
    }
    if (m_util.str.is_empty(a)) {
        result = b;
        return BR_DONE;
    }
    if (m_util.str.is_empty(b)) {
        result = a;
        return BR_DONE;
    }
    if (m_util.str.is_concat(a, c, d) && 
        m_util.str.is_string(d, s1) && isc2) {
        result = m_util.str.mk_concat(c, m_util.str.mk_string(s1 + s2));
        return BR_DONE;
    }
    return BR_FAILED;
}

br_status seq_rewriter::mk_str_length(expr* a, expr_ref& result) {
    std::string b;
    m_es.reset();
    m_util.str.get_concat(a, m_es);
    size_t len = 0;
    unsigned j = 0;
    for (unsigned i = 0; i < m_es.size(); ++i) {
        if (m_util.str.is_string(m_es[i], b)) {
            len += b.length();
        }
        else {
            m_es[j] = m_es[i];
            ++j;
        }
    }
    if (j == 0) {
        result = m_autil.mk_numeral(rational(len, rational::ui64()), true);
        return BR_DONE;
    }
    if (j != m_es.size() || j != 1) {
        expr_ref_vector es(m());        
        for (unsigned i = 0; i < j; ++i) {
            es.push_back(m_util.str.mk_length(m_es[i]));
        }
        if (len != 0) {
            es.push_back(m_autil.mk_numeral(rational(len, rational::ui64()), true));
        }
        result = m_autil.mk_add(es.size(), es.c_ptr());
        return BR_DONE;
    }
    return BR_FAILED;
}

br_status seq_rewriter::mk_str_substr(expr* a, expr* b, expr* c, expr_ref& result) {
    std::string s;
    rational pos, len;
    if (m_util.str.is_string(a, s) && m_autil.is_numeral(b, pos) && m_autil.is_numeral(c, len) &&
        pos.is_unsigned() && len.is_unsigned() && pos.get_unsigned() <= s.length()) {
        unsigned _pos = pos.get_unsigned();
        unsigned _len = len.get_unsigned();
        result = m_util.str.mk_string(s.substr(_pos, _len));
        return BR_DONE;
    }
    return BR_FAILED;
}
br_status seq_rewriter::mk_str_strctn(expr* a, expr* b, expr_ref& result) {
    std::string c, d;
    if (m_util.str.is_string(a, c) && m_util.str.is_string(b, d)) {
        result = m().mk_bool_val(0 != strstr(d.c_str(), c.c_str()));
        return BR_DONE;
    }
    return BR_FAILED;
}

br_status seq_rewriter::mk_str_at(expr* a, expr* b, expr_ref& result) {
    std::string c;
    rational r;
    if (m_util.str.is_string(a, c) && m_autil.is_numeral(b, r) && r.is_unsigned()) {
        unsigned j = r.get_unsigned();
        if (j < c.length()) {
            char ch = c[j];
            c[0] = ch;
            c[1] = 0;
            result = m_util.str.mk_string(c);
            return BR_DONE;
        }
    }
    return BR_FAILED;
}

br_status seq_rewriter::mk_str_stridof(expr* a, expr* b, expr* c, expr_ref& result) {
    std::string s1, s2;
    rational r;
    bool isc1 = m_util.str.is_string(a, s1);
    bool isc2 = m_util.str.is_string(b, s2);

    if (isc1 && isc2 && m_autil.is_numeral(c, r) && r.is_unsigned()) {
        for (unsigned i = r.get_unsigned(); i < s1.length(); ++i) {
            if (strncmp(s1.c_str() + i, s2.c_str(), s2.length()) == 0) {
                result = m_autil.mk_numeral(rational(i) - r, true);
                return BR_DONE;
            }
        }
        result = m_autil.mk_numeral(rational(-1), true);
        return BR_DONE;
    }
    if (m_autil.is_numeral(c, r) && r.is_neg()) {
        result = m_autil.mk_numeral(rational(-1), true);
        return BR_DONE;
    }
    
    if (m_util.str.is_empty(b)) {
        result = c;
        return BR_DONE;
    }
    // Enhancement: walk segments of a, determine which segments must overlap, must not overlap, may overlap.
    return BR_FAILED;
}

br_status seq_rewriter::mk_str_strrepl(expr* a, expr* b, expr* c, expr_ref& result) {
    std::string s1, s2, s3;
    if (m_util.str.is_string(a, s1) && m_util.str.is_string(b, s2) && 
        m_util.str.is_string(c, s3)) {
        std::ostringstream buffer;
        for (size_t i = 0; i < s1.length(); ) {
            if (strncmp(s1.c_str() + i, s2.c_str(), s2.length()) == 0) {
                buffer << s3;
                i += s2.length();
            }
            else {
                buffer << s1[i];
                ++i;
            }
        }
        result = m_util.str.mk_string(buffer.str());
        return BR_DONE;
    }
    if (b == c) {
        result = a;
        return BR_DONE;
    }
    return BR_FAILED;
}

br_status seq_rewriter::mk_seq_prefix(expr* a, expr* b, expr_ref& result) {
    std::string s1, s2;
    bool isc1 = m_util.str.is_string(a, s1);
    bool isc2 = m_util.str.is_string(b, s2);
    if (isc1 && isc2) {
        bool prefix = s1.length() <= s2.length();
        for (unsigned i = 0; i < s1.length() && prefix; ++i) {
            prefix = s1[i] == s2[i];
        }
        result = m().mk_bool_val(prefix);
        return BR_DONE;
    }
    if (m_util.str.is_empty(a)) {
        result = m().mk_true();
        return BR_DONE;
    }
    return BR_FAILED;
}

br_status seq_rewriter::mk_seq_suffix(expr* a, expr* b, expr_ref& result) {
    std::string s1, s2;
    bool isc1 = m_util.str.is_string(a, s1);
    if (isc1 && m_util.str.is_string(b, s2)) {
        bool suffix = s1.length() <= s2.length();
        for (unsigned i = 0; i < s1.length() && suffix; ++i) {
            suffix = s1[s1.length() - i - 1] == s2[s2.length() - i - 1];
        }
        result = m().mk_bool_val(suffix);
        return BR_DONE;
    }
    if (m_util.str.is_empty(a)) {
        result = m().mk_true();
        return BR_DONE;
    }
    return BR_FAILED;
}

br_status seq_rewriter::mk_str_itos(expr* a, expr_ref& result) {
    rational r;
    if (m_autil.is_numeral(a, r)) {
        result = m_util.str.mk_string(r.to_string());
        return BR_DONE;
    }
    return BR_FAILED;
}
br_status seq_rewriter::mk_str_stoi(expr* a, expr_ref& result) {
    std::string s;
    if (m_util.str.is_string(a, s)) {
        for (unsigned i = 0; i < s.length(); ++i) {
            if (s[i] == '-') { if (i != 0) return BR_FAILED; }
            else if ('0' <= s[i] && s[i] <= '9') continue;
            return BR_FAILED;            
        }
        rational r(s.c_str());
        result = m_autil.mk_numeral(r, true);
        return BR_DONE;
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
