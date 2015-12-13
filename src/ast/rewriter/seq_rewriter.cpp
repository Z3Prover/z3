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
#include"ast_util.h"
#include"uint_set.h"


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
    case _OP_SEQ_SKOLEM:
        return BR_FAILED;
    
    case OP_SEQ_CONCAT: 
        if (num_args == 1) {
            result = args[0];
            return BR_DONE;
        }
        SASSERT(num_args == 2);
        return mk_seq_concat(args[0], args[1], result);
    case OP_SEQ_LENGTH:
        SASSERT(num_args == 1);
        return mk_seq_length(args[0], result);
    case OP_SEQ_EXTRACT:
        SASSERT(num_args == 3);
        return mk_seq_extract(args[0], args[1], args[2], result);
    case OP_SEQ_CONTAINS: 
        SASSERT(num_args == 2);
        return mk_seq_contains(args[0], args[1], result);
    case OP_SEQ_AT:
        SASSERT(num_args == 2);
        return mk_seq_at(args[0], args[1], result); 
    case OP_SEQ_PREFIX: 
        SASSERT(num_args == 2);
        return mk_seq_prefix(args[0], args[1], result);
    case OP_SEQ_SUFFIX: 
        SASSERT(num_args == 2);
        return mk_seq_suffix(args[0], args[1], result);
    case OP_SEQ_INDEX:
        if (num_args == 2) {
            expr_ref arg3(m_autil.mk_int(0), m());
            result = m_util.str.mk_index(args[0], args[1], arg3);
            return BR_REWRITE1;
        }
        SASSERT(num_args == 3);
        return mk_seq_index(args[0], args[1], args[2], result);
    case OP_SEQ_REPLACE:
        SASSERT(num_args == 3);
        return mk_seq_replace(args[0], args[1], args[2], result);
    case OP_SEQ_TO_RE:
        return BR_FAILED;
    case OP_SEQ_IN_RE:
        return BR_FAILED;

    case OP_STRING_CONST:
        return BR_FAILED;
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
    case _OP_STRING_STRREPL:
    case _OP_STRING_STRIDOF: 
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
    zstring s1, s2;
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

br_status seq_rewriter::mk_seq_length(expr* a, expr_ref& result) {
    zstring b;
    m_es.reset();
    m_util.str.get_concat(a, m_es);
    unsigned len = 0;
    unsigned j = 0;
    for (unsigned i = 0; i < m_es.size(); ++i) {
        if (m_util.str.is_string(m_es[i], b)) {
            len += b.length();
        }
        else if (m_util.str.is_unit(m_es[i])) {
            len += 1;
        }
        else if (m_util.str.is_empty(m_es[i])) {
            // skip
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

br_status seq_rewriter::mk_seq_extract(expr* a, expr* b, expr* c, expr_ref& result) {
    zstring s;
    rational pos, len;
    if (m_util.str.is_string(a, s) && m_autil.is_numeral(b, pos) && m_autil.is_numeral(c, len) &&
        pos.is_unsigned() && len.is_unsigned() && pos.get_unsigned() <= s.length()) {
        unsigned _pos = pos.get_unsigned();
        unsigned _len = len.get_unsigned();
        result = m_util.str.mk_string(s.extract(_pos, _len));
        return BR_DONE;
    }
    return BR_FAILED;
}
br_status seq_rewriter::mk_seq_contains(expr* a, expr* b, expr_ref& result) {
    zstring c, d;
    if (m_util.str.is_string(a, c) && m_util.str.is_string(b, d)) {
        result = m().mk_bool_val(c.contains(d));
        return BR_DONE;
    }
    // check if subsequence of b is in a.
    ptr_vector<expr> as, bs;
    m_util.str.get_concat(a, as);
    m_util.str.get_concat(b, bs);
    bool found = false;
    for (unsigned i = 0; !found && i < as.size(); ++i) {
        if (bs.size() > as.size() - i) break;
        unsigned j = 0;
        for (; j < bs.size() && as[j+i] == bs[j]; ++j) {};
        found = j == bs.size();
    }
    if (found) {
        result = m().mk_true();
        return BR_DONE;
    }
    return BR_FAILED;
}

br_status seq_rewriter::mk_seq_at(expr* a, expr* b, expr_ref& result) {
    zstring c;
    rational r;
    if (m_util.str.is_string(a, c) && m_autil.is_numeral(b, r) && r.is_unsigned()) {
        unsigned j = r.get_unsigned();
        if (j < c.length()) {
            result = m_util.str.mk_string(c.extract(j, 1));
            return BR_DONE;
        }
    }
    return BR_FAILED;
}

br_status seq_rewriter::mk_seq_index(expr* a, expr* b, expr* c, expr_ref& result) {
    zstring s1, s2;
    rational r;
    bool isc1 = m_util.str.is_string(a, s1);
    bool isc2 = m_util.str.is_string(b, s2);

    if (isc1 && isc2 && m_autil.is_numeral(c, r) && r.is_unsigned()) {
        int idx = s1.indexof(s2, r.get_unsigned());
        result = m_autil.mk_numeral(rational(idx), true);
        return BR_DONE;
    }
    if (m_autil.is_numeral(c, r) && r.is_neg()) {
        result = m_autil.mk_numeral(rational(-1), true);
        return BR_DONE;
    }
    
    if (m_util.str.is_empty(b) && m_autil.is_numeral(c, r) && r.is_zero()) {
        result = c;
        return BR_DONE;
    }
    // Enhancement: walk segments of a, determine which segments must overlap, must not overlap, may overlap.
    return BR_FAILED;
}

br_status seq_rewriter::mk_seq_replace(expr* a, expr* b, expr* c, expr_ref& result) {
    zstring s1, s2, s3;
    if (m_util.str.is_string(a, s1) && m_util.str.is_string(b, s2) && 
        m_util.str.is_string(c, s3)) {
        result = m_util.str.mk_string(s1.replace(s2, s3));
        return BR_DONE;
    }
    if (b == c) {
        result = a;
        return BR_DONE;
    }
    return BR_FAILED;
}

br_status seq_rewriter::mk_seq_prefix(expr* a, expr* b, expr_ref& result) {
    TRACE("seq", tout << mk_pp(a, m()) << " " << mk_pp(b, m()) << "\n";);
    zstring s1, s2;
    bool isc1 = m_util.str.is_string(a, s1);
    bool isc2 = m_util.str.is_string(b, s2);
    if (isc1 && isc2) {
        result = m().mk_bool_val(s1.prefixof(s2));
        return BR_DONE;
    }
    if (m_util.str.is_empty(a)) {
        result = m().mk_true();
        return BR_DONE;
    }
    expr* a1 = m_util.str.get_leftmost_concat(a);
    expr* b1 = m_util.str.get_leftmost_concat(b);
    isc1 = m_util.str.is_string(a1, s1);
    isc2 = m_util.str.is_string(b1, s2);
    ptr_vector<expr> as, bs;

    if (a1 != b1 && isc1 && isc2) {
        if (s1.length() <= s2.length()) {
            if (s1.prefixof(s2)) {
                if (a == a1) {
                    result = m().mk_true();
                    return BR_DONE;
                }               
                m_util.str.get_concat(a, as);
                m_util.str.get_concat(b, bs);
                SASSERT(as.size() > 1);
                s2 = s2.extract(s1.length(), s2.length()-s1.length());
                bs[0] = m_util.str.mk_string(s2);
                result = m_util.str.mk_prefix(m_util.str.mk_concat(as.size()-1, as.c_ptr()+1),
                                              m_util.str.mk_concat(bs.size(), bs.c_ptr()));
                return BR_REWRITE_FULL;
            }
            else {
                result = m().mk_false();
                return BR_DONE;
            }
        }
        else {
            if (s2.prefixof(s1)) {
                if (b == b1) {
                    result = m().mk_false();
                    return BR_DONE;
                }
                m_util.str.get_concat(a, as);
                m_util.str.get_concat(b, bs);
                SASSERT(bs.size() > 1);
                s1 = s1.extract(s2.length(), s1.length() - s2.length());
                as[0] = m_util.str.mk_string(s1);
                result = m_util.str.mk_prefix(m_util.str.mk_concat(as.size(), as.c_ptr()),
                                     m_util.str.mk_concat(bs.size()-1, bs.c_ptr()+1));
                return BR_REWRITE_FULL;                
            }
            else {
                result = m().mk_false();
                return BR_DONE;
            }
        }        
    }
    if (a1 != b1) {
        return BR_FAILED;
    }
    m_util.str.get_concat(a, as);
    m_util.str.get_concat(b, bs);
    unsigned i = 0;
    for (; i < as.size() && i < bs.size() && as[i] == bs[i]; ++i) {};
    if (i == as.size()) {
        result = m().mk_true();
        return BR_DONE;
    }
    if (i == bs.size()) {
        expr_ref_vector es(m());
        for (unsigned j = i; j < as.size(); ++j) {
            es.push_back(m().mk_eq(m_util.str.mk_empty(m().get_sort(a)), as[j]));
        }
        result = mk_and(es);
        return BR_REWRITE3;
    }
    if (i > 0) {
        SASSERT(i < as.size() && i < bs.size());
        a = m_util.str.mk_concat(as.size() - i, as.c_ptr() + i);
        b = m_util.str.mk_concat(bs.size() - i, bs.c_ptr() + i); 
        result = m_util.str.mk_prefix(a, b);
        return BR_DONE;
    }
    UNREACHABLE();
    return BR_FAILED;
}

br_status seq_rewriter::mk_seq_suffix(expr* a, expr* b, expr_ref& result) {
    if (a == b) {
        result = m().mk_true();
        return BR_DONE;
    }
    zstring s1, s2;
    if (m_util.str.is_empty(a)) {
        result = m().mk_true();
        return BR_DONE;
    }
    if (m_util.str.is_empty(b)) {
        result = m().mk_eq(m_util.str.mk_empty(m().get_sort(a)), a);
        return BR_REWRITE3;
    }
    // concatenation is left-associative, so a2, b2 are not concatenations
    expr* a1, *a2, *b1, *b2;
    if (m_util.str.is_concat(a, a1, a2) && 
        m_util.str.is_concat(b, b1, b2) && a2 == b2) {
        result = m_util.str.mk_suffix(a1, b1);
        return BR_REWRITE1;
    }
    if (m_util.str.is_concat(b, b1, b2) && b2 == a) {
        result = m().mk_true();
        return BR_DONE;
    }
    bool isc1 = false;
    bool isc2 = false;
    
    if (m_util.str.is_concat(a, a1, a2) && m_util.str.is_string(a2, s1)) {
        isc1 = true;
    }
    else if (m_util.str.is_string(a, s1)) {
        isc1 = true;
        a2 = a;
        a1 = 0;
    }

    if (m_util.str.is_concat(b, b1, b2) && m_util.str.is_string(b2, s2)) {
        isc2 = true;
    }
    else if (m_util.str.is_string(b, s2)) {
        isc2 = true;
        b2 = b;
        b1 = 0;
    }
    if (isc1 && isc2) {
        if (s1.length() == s2.length()) {
            //SASSERT(s1 != s2);
            result = m().mk_false();
            return BR_DONE;
        }
        else if (s1.length() < s2.length()) {
            bool suffix = s1.suffixof(s2);
            if (suffix && a1 == 0) {
                result = m().mk_true();
                return BR_DONE;
            }
            else if (suffix) {
                s2 = s2.extract(0, s2.length()-s1.length());
                b2 = m_util.str.mk_string(s2);
                result = m_util.str.mk_suffix(a1, b1?m_util.str.mk_concat(b1, b2):b2);
                return BR_DONE;
            }
            else {
                result = m().mk_false();
                return BR_DONE;
            }
        }
        else {
            SASSERT(s1.length() > s2.length());
            if (b1 == 0) {
                result = m().mk_false();
                return BR_DONE;
            }
            bool suffix = s2.suffixof(s1);
            if (suffix) {
                s1 = s1.extract(0, s1.length()-s2.length());
                a2 = m_util.str.mk_string(s1);
                result = m_util.str.mk_suffix(a1?m_util.str.mk_concat(a1, a2):a2, b1);
                return BR_DONE;
            }
            else {
                result = m().mk_false();
                return BR_DONE;
            }            
        }
    }

    return BR_FAILED;
}

br_status seq_rewriter::mk_str_itos(expr* a, expr_ref& result) {
    rational r;
    if (m_autil.is_numeral(a, r)) {
        result = m_util.str.mk_string(symbol(r.to_string().c_str()));
        return BR_DONE;
    }
    return BR_FAILED;
}
br_status seq_rewriter::mk_str_stoi(expr* a, expr_ref& result) {
    zstring str;
    if (m_util.str.is_string(a, str)) {
        std::string s = str.encode();
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

br_status seq_rewriter::mk_eq_core(expr * l, expr * r, expr_ref & result) {
    expr_ref_vector lhs(m()), rhs(m()), res(m());
    if (!reduce_eq(l, r, lhs, rhs)) {
        result = m().mk_false();
        return BR_DONE;
    }
    if (lhs.size() == 1 && lhs[0].get() == l && rhs[0].get() == r) {
        return BR_FAILED;
    }
    for (unsigned i = 0; i < lhs.size(); ++i) {
        res.push_back(m().mk_eq(lhs[i].get(), rhs[i].get()));
    }
    result = mk_and(res);
    return BR_REWRITE3;
}

bool seq_rewriter::reduce_eq(expr* l, expr* r, expr_ref_vector& lhs, expr_ref_vector& rhs) {
    expr* a, *b;
    bool change = false;
    expr_ref_vector trail(m());
    m_lhs.reset();
    m_rhs.reset();
    m_util.str.get_concat(l, m_lhs);
    m_util.str.get_concat(r, m_rhs);
 
    // solve from back
    while (!m_lhs.empty() && !m_rhs.empty()) {
        if (m_lhs.back() == m_rhs.back()) {
            m_lhs.pop_back();
            m_rhs.pop_back();
        }
        else if(m_util.str.is_unit(m_lhs.back(), a) &&
                m_util.str.is_unit(m_rhs.back(), b)) {
            lhs.push_back(a);
            rhs.push_back(b);
            m_lhs.pop_back();
            m_rhs.pop_back();
        }
        else if (!m_rhs.empty() && m_util.str.is_empty(m_rhs.back())) {
            m_rhs.pop_back();
        }
        else if (!m_lhs.empty() && m_util.str.is_empty(m_lhs.back())) {
            m_lhs.pop_back();
        }
        else {
            break;
        }
        change = true;
    }

    // solve from front
    unsigned head1 = 0, head2 = 0;
    while (head1 < m_lhs.size() && head2 < m_rhs.size()) {
        if (m_lhs[head1] == m_rhs[head2]) {
            ++head1;
            ++head2;
        }
        else if(m_util.str.is_unit(m_lhs[head1], a) &&
                m_util.str.is_unit(m_rhs[head2], b)) {
            lhs.push_back(a);
            rhs.push_back(b);
            ++head1;
            ++head2;
        }
        else if (head1 < m_lhs.size() && m_util.str.is_empty(m_lhs[head1])) {
            ++head1;
        }
        else if (head2 < m_rhs.size() && m_util.str.is_empty(m_rhs[head2])) {
            ++head2;
        }
        else {
            break;
        }
        change = true;
    }
    // reduce strings
    zstring s1, s2;
    while (head1 < m_lhs.size() && 
           head2 < m_rhs.size() && 
           m_util.str.is_string(m_lhs[head1], s1) &&
           m_util.str.is_string(m_rhs[head2], s2)) {
        unsigned l = std::min(s1.length(), s2.length());
        for (unsigned i = 0; i < l; ++i) {
            if (s1[i] != s2[i]) {
                return false;
            }
        }
        if (l == s1.length()) {
            ++head1;            
        }
        else {
            m_lhs[head1] = m_util.str.mk_string(s1.extract(l, s1.length()-l));
            trail.push_back(m_lhs[head1]);
        }
        if (l == s2.length()) {
            ++head2;            
        }
        else {
            m_rhs[head2] = m_util.str.mk_string(s2.extract(l, s2.length()-l));
            trail.push_back(m_rhs[head2]);
        }
        change = true;
    }
    while (head1 < m_lhs.size() && 
           head2 < m_rhs.size() &&
           m_util.str.is_string(m_lhs.back(), s1) &&
           m_util.str.is_string(m_rhs.back(), s2)) {
        unsigned l = std::min(s1.length(), s2.length());
        for (unsigned i = 0; i < l; ++i) {
            if (s1[s1.length()-i-1] != s2[s2.length()-i-1]) {
                return false;
            }
        }
        m_lhs.pop_back();          
        m_rhs.pop_back();
        if (l < s1.length()) {
            m_lhs.push_back(m_util.str.mk_string(s1.extract(0, s1.length()-l)));
            trail.push_back(m_lhs.back());
        }
        if (l < s2.length()) {
            m_rhs.push_back(m_util.str.mk_string(s2.extract(0, s2.length()-l)));
            trail.push_back(m_rhs.back());
        }
        change = true;
    }

    bool is_sat;
    unsigned szl = m_lhs.size() - head1, szr = m_rhs.size() - head2;
    expr* const* ls = m_lhs.c_ptr() + head1, * const*rs = m_rhs.c_ptr() + head2;
    if (length_constrained(szl, ls, szr, rs, lhs, rhs, is_sat)) {
        return is_sat;
    }
    if (is_subsequence(szl, ls, szr, rs, lhs, rhs, is_sat)) {
        return is_sat;
    }

	if (szl == 0 && szr == 0) {
		return true;
	}
    else if (!change) {
        lhs.push_back(l);
        rhs.push_back(r);
    }
    else {
        // could solve if either side is fixed size.
        SASSERT(szl > 0 && szr > 0);

        lhs.push_back(m_util.str.mk_concat(szl, ls));
        rhs.push_back(m_util.str.mk_concat(szr, rs));
    }
    return true;
}

expr* seq_rewriter::concat_non_empty(unsigned n, expr* const* as) {
    SASSERT(n > 0);
    ptr_vector<expr> bs;
    for (unsigned i = 0; i < n; ++i) {
        if (m_util.str.is_unit(as[i]) ||
            m_util.str.is_string(as[i])) {
            bs.push_back(as[i]);
        }
    }    
    if (bs.empty()) {
        return m_util.str.mk_empty(m().get_sort(as[0]));
    }
    else {
        return m_util.str.mk_concat(bs.size(), bs.c_ptr());
    }
}

bool seq_rewriter::set_empty(unsigned sz, expr* const* es, bool all, expr_ref_vector& lhs, expr_ref_vector& rhs) {
    zstring s;
    for (unsigned i = 0; i < sz; ++i) {
        if (m_util.str.is_unit(es[i])) {
            if (all) return false;
        }
        else if (m_util.str.is_empty(es[i])) {
            continue;
        }
        else if (m_util.str.is_string(es[i], s)) {
            if (all) {
                SASSERT(s.length() > 0);
                return false;
            }
        }
        else {
            lhs.push_back(m_util.str.mk_empty(m().get_sort(es[i])));
            rhs.push_back(es[i]);
        }
    }
    return true;
}

bool seq_rewriter::min_length(unsigned n, expr* const* es, unsigned& len) {
    zstring s;
    bool bounded = true;
    len = 0;
    for (unsigned i = 0; i < n; ++i) {
        if (m_util.str.is_unit(es[i])) {
            ++len;
        }
        else if (m_util.str.is_empty(es[i])) {
            continue;
        }
        else if (m_util.str.is_string(es[i], s)) {
            len += s.length();
        }
        else {
            bounded = false;
        }
    }
    return bounded;
}

bool seq_rewriter::length_constrained(unsigned szl, expr* const* l, unsigned szr, expr* const* r, 
                                      expr_ref_vector& lhs, expr_ref_vector& rhs, bool& is_sat) {
    is_sat = true;
    unsigned len1 = 0, len2 = 0;
    bool bounded1 = min_length(szl, l, len1);
    bool bounded2 = min_length(szr, r, len2);
    if (bounded1 && len1 < len2) {
        is_sat = false;
        return true;
    }
    if (bounded2 && len2 < len1) {
        is_sat = false;
        return true;
    }
    if (bounded1 && len1 == len2 && len1 > 0) {
        is_sat = set_empty(szr, r, false, lhs, rhs);
        if (is_sat) {
            lhs.push_back(concat_non_empty(szl, l));
            rhs.push_back(concat_non_empty(szr, r));
        }
        return true;
    }
    if (bounded2 && len1 == len2 && len1 > 0) {
        is_sat = set_empty(szl, l, false, lhs, rhs);
        if (is_sat) {
            lhs.push_back(concat_non_empty(szl, l));
            rhs.push_back(concat_non_empty(szr, r));
        }
        return true;
    }
    
    return false;
}

bool seq_rewriter::is_subsequence(unsigned szl, expr* const* l, unsigned szr, expr* const* r, 
                                  expr_ref_vector& lhs, expr_ref_vector& rhs, bool& is_sat) {
    is_sat = true;
    if (szl == szr) return false;
    if (szr < szl) {
        std::swap(szl, szr);
        std::swap(l, r);
    }

    uint_set rpos;
    for (unsigned i = 0; i < szl; ++i) {
        bool found = false;
        unsigned j = 0;
        for (; !found && j < szr; ++j) {
            found = !rpos.contains(j) && l[i] == r[j];
        }
        if (!found) {
            return false;
        }
        SASSERT(0 < j && j <= szr);
        rpos.insert(j-1);
    }
    // if we reach here, then every element of l is contained in r in some position.
    ptr_vector<expr> rs;
    for (unsigned j = 0; j < szr; ++j) {
        if (rpos.contains(j)) {
            rs.push_back(r[j]);
        }
        else if (!set_empty(1, r + j, true, lhs, rhs)) {
            is_sat = false;
            return true;
        }
    }
    SASSERT(szl == rs.size());
    if (szl > 0) {
        lhs.push_back(m_util.str.mk_concat(szl, l));
        rhs.push_back(m_util.str.mk_concat(szl, rs.c_ptr()));
    }
    return true;
} 
