/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    seq_axioms.cpp

Abstract:

    Axiomatize string operations that can be reduced to 
    more basic operations. These axioms are kept outside
    of a particular solver: they are mainly solver independent.

Author:

    Nikolaj Bjorner (nbjorner) 2020-4-16

Revision History:

--*/

#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include "smt/seq_axioms.h"
#include "smt/smt_context.h"

using namespace smt;

seq_axioms::seq_axioms(theory& th, th_rewriter& r):
    th(th),
    m_rewrite(r),
    m(r.m()),
    a(m),
    seq(m),
    m_sk(m, r)
{}

literal seq_axioms::mk_eq(expr* a, expr* b) {
    return th.mk_eq(a, b, false);
}

expr_ref seq_axioms::mk_sub(expr* x, expr* y) {
    expr_ref result(a.mk_sub(x, y), m);
    m_rewrite(result);
    return result;
}


literal seq_axioms::mk_literal(expr* _e) {
    expr_ref e(_e, m);
    if (a.is_arith_expr(e)) {
        m_rewrite(e);
    }
    th.ensure_enode(e);
    return ctx().get_literal(e);
}

/*

  let e = extract(s, i, l)

  i is start index, l is length of substring starting at index.

  i < 0 => e = ""
  i >= |s| => e = ""
  l <= 0 => e = ""
  0 <= i < |s| & l > 0 => s = xey, |x| = i, |e| = min(l, |s|-i)
  l <= 0 => e = ""

this translates to:

  0 <= i <= |s| -> s = xey 
  0 <= i <= |s| -> len(x) = i
  0 <= i <= |s| & 0 <= l <= |s| - i -> |e| = l
  0 <= i <= |s| & |s| < l + i  -> |e| = |s| - i
  |e| = 0 <=> i < 0 | |s| <= i | l <= 0 | |s| <= 0

  It follows that: 
  |e| = min(l, |s| - i) for 0 <= i < |s| and 0 < |l|


*/


void seq_axioms::add_extract_axiom(expr* e) {
    TRACE("seq", tout << mk_pp(e, m) << "\n";);
    expr* s = nullptr, *i = nullptr, *l = nullptr;
    VERIFY(seq.str.is_extract(e, s, i, l));
    if (is_tail(s, i, l)) {
        add_tail_axiom(e, s);
        return;
    }
    if (is_drop_last(s, i, l)) {
        add_drop_last_axiom(e, s);
        return;
    }
    if (is_extract_prefix0(s, i, l)) {
        add_extract_prefix_axiom(e, s, l);
        return;
    }
    if (is_extract_suffix(s, i, l)) {
        add_extract_suffix_axiom(e, s, i);
        return;
    }
    expr_ref x = m_sk.mk_pre(s, i);
    expr_ref ls = mk_len(s);
    expr_ref lx = mk_len(x);
    expr_ref le = mk_len(e);
    expr_ref ls_minus_i_l(mk_sub(mk_sub(ls, i), l), m);
    expr_ref y = m_sk.mk_post(s, a.mk_add(i, l));
    expr_ref xe = mk_concat(x, e);
    expr_ref xey = mk_concat(x, e, y);
    expr_ref zero(a.mk_int(0), m);

    literal i_ge_0    = mk_literal(a.mk_ge(i, zero));
    literal i_le_ls   = mk_literal(a.mk_le(mk_sub(i, ls), zero));
    literal ls_le_i   = mk_literal(a.mk_le(mk_sub(ls, i), zero));
    literal ls_ge_li  = mk_literal(a.mk_ge(ls_minus_i_l, zero));
    literal l_ge_0    = mk_literal(a.mk_ge(l, zero));
    literal l_le_0    = mk_literal(a.mk_le(l, zero));
    literal ls_le_0   = mk_literal(a.mk_le(ls, zero));
    literal le_is_0   = mk_eq(le, zero);


    // 0 <= i & i <= |s| & 0 <= l => xey = s
    // 0 <= i & i <= |s| => |x| = i
    // 0 <= i & i <= |s| & l >= 0 & |s| >= l + i => |e| = l
    // 0 <= i & i <= |s| & |s| < l + i => |e| = |s| - i
    // i < 0 => |e| = 0
    // |s| <= i => |e| = 0
    // |s| <= 0 => |e| = 0
    // l <= 0 => |e| = 0
    // |e| = 0 & i >= 0 & |s| > i & |s| > 0 => l <= 0
    add_axiom(~i_ge_0, ~i_le_ls, ~l_ge_0, mk_seq_eq(xey, s));
    add_axiom(~i_ge_0, ~i_le_ls, mk_eq(lx, i));
    add_axiom(~i_ge_0, ~i_le_ls, ~l_ge_0, ~ls_ge_li, mk_eq(le, l));
    add_axiom(~i_ge_0, ~i_le_ls, ~l_ge_0, ls_ge_li, mk_eq(le, mk_sub(ls, i)));
    add_axiom(i_ge_0,   le_is_0);
    add_axiom(~ls_le_i, le_is_0);
    add_axiom(~ls_le_0, le_is_0);
    add_axiom(~l_le_0,  le_is_0);
    add_axiom(~le_is_0, ~i_ge_0, ls_le_i, ls_le_0, l_le_0);
}

void seq_axioms::add_tail_axiom(expr* e, expr* s) {    
    expr_ref head(m), tail(m);
    m_sk.decompose(s, head, tail);
    TRACE("seq", tout << "tail " << mk_bounded_pp(e, m, 2) << " " << mk_bounded_pp(s, m, 2) << "\n";);
    literal emp = mk_eq_empty(s);
    add_axiom(emp, mk_seq_eq(s, mk_concat(head, e)));
    add_axiom(~emp, mk_eq_empty(e));
}

void seq_axioms::add_drop_last_axiom(expr* e, expr* s) {
    TRACE("seq", tout << "drop last " << mk_bounded_pp(e, m, 2) << " " << mk_bounded_pp(s, m, 2) << "\n";);
    literal emp = mk_eq_empty(s);
    add_axiom(emp, mk_seq_eq(s, mk_concat(e, seq.str.mk_unit(m_sk.mk_last(s)))));
    add_axiom(~emp, mk_eq_empty(e));
}

bool seq_axioms::is_drop_last(expr* s, expr* i, expr* l) {
    rational i1;
    if (!a.is_numeral(i, i1) || !i1.is_zero()) {
        return false;
    }
    expr_ref l2(m), l1(l, m);
    l2 = mk_sub(mk_len(s), a.mk_int(1));
    m_rewrite(l1);
    m_rewrite(l2);
    return l1 == l2;
}

bool seq_axioms::is_tail(expr* s, expr* i, expr* l) {
    rational i1;
    if (!a.is_numeral(i, i1) || !i1.is_one()) {
        return false;
    }
    expr_ref l2(m), l1(l, m);
    l2 = mk_sub(mk_len(s), a.mk_int(1));
    m_rewrite(l1);
    m_rewrite(l2);
    return l1 == l2;
}

bool seq_axioms::is_extract_prefix0(expr* s, expr* i, expr* l) {
    rational i1;
    return a.is_numeral(i, i1) && i1.is_zero();    
}

bool seq_axioms::is_extract_suffix(expr* s, expr* i, expr* l) {
    expr_ref len(a.mk_add(l, i), m);
    m_rewrite(len);
    return seq.str.is_length(len, l) && l == s;
}

/*
  0 <= l <= len(s) => s = ey & l = len(e)
  len(s) < l => s = e
  l < 0 => e = empty
 */
void seq_axioms::add_extract_prefix_axiom(expr* e, expr* s, expr* l) {
    TRACE("seq", tout << "prefix " << mk_bounded_pp(e, m, 2) << " " << mk_bounded_pp(s, m, 2) << " " << mk_bounded_pp(l, m, 2) << "\n";);
    expr_ref le = mk_len(e);
    expr_ref ls = mk_len(s);
    expr_ref ls_minus_l(mk_sub(ls, l), m);
    expr_ref zero(a.mk_int(0), m);
    expr_ref y = m_sk.mk_post(s, l);
    expr_ref ey = mk_concat(e, y);
    literal l_ge_0 = mk_literal(a.mk_ge(l, zero));
    literal l_le_s = mk_literal(a.mk_le(mk_sub(l, ls), zero));
    add_axiom(~l_ge_0, ~l_le_s, mk_seq_eq(s, ey));
    add_axiom(~l_ge_0, ~l_le_s, mk_eq(l, le));
    add_axiom(~l_ge_0, ~l_le_s, mk_eq(ls_minus_l, mk_len(y)));
    add_axiom(l_le_s, mk_eq(e, s));
    add_axiom(l_ge_0, mk_eq_empty(e));
}

/*
  0 <= i <= len(s) => s = xe & i = len(x)    
  i < 0 => e = empty
  i > len(s) => e = empty
 */
void seq_axioms::add_extract_suffix_axiom(expr* e, expr* s, expr* i) {
    TRACE("seq", tout << "suffix " << mk_bounded_pp(e, m, 2) << " " << mk_bounded_pp(s, m, 2) << "\n";);
    expr_ref x = m_sk.mk_pre(s, i);
    expr_ref lx = mk_len(x);
    expr_ref ls = mk_len(s);
    expr_ref zero(a.mk_int(0), m);
    expr_ref xe = mk_concat(x, e);
    literal le_is_0 = mk_eq_empty(e);
    literal i_ge_0 = mk_literal(a.mk_ge(i, zero));
    literal i_le_s = mk_literal(a.mk_le(mk_sub(i, ls), zero));
    add_axiom(~i_ge_0, ~i_le_s, mk_seq_eq(s, xe));
    add_axiom(~i_ge_0, ~i_le_s, mk_eq(i, lx));
    add_axiom(i_ge_0, le_is_0);
    add_axiom(i_le_s, le_is_0);
}        

/*
  encode that s is not contained in of xs1
  where s1 is all of s, except the last element.
  
  s = "" or s = s1*(unit c)
  s = "" or !contains(x*s1, s)
*/
void seq_axioms::tightest_prefix(expr* s, expr* x) {
    expr_ref s1 = m_sk.mk_first(s);
    expr_ref c  = m_sk.mk_last(s);
    expr_ref s1c = mk_concat(s1, seq.str.mk_unit(c));
    literal s_eq_emp = mk_eq_empty(s);
    add_axiom(s_eq_emp, mk_seq_eq(s, s1c));
    add_axiom(s_eq_emp, ~mk_literal(seq.str.mk_contains(mk_concat(x, s1), s)));
}

/*
    [[str.indexof]](w, w2, i) is the smallest n such that for some some w1, w3
    - w = w1w2w3
    - i <= n = |w1|

    if [[str.contains]](w, w2) = true, |w2| > 0 and i >= 0.

    [[str.indexof]](w,w2,i) = -1  otherwise.


  let i = Index(t, s, offset):
  // index of s in t starting at offset.

  
  |t| = 0 => |s| = 0 or indexof(t,s,offset) = -1
  |t| = 0 & |s| = 0 => indexof(t,s,offset) = 0

  offset >= len(t) => |s| = 0 or i = -1
  
  len(t) != 0 & !contains(t, s) => i = -1


  offset = 0 & len(t) != 0 & contains(t, s) => t = xsy & i = len(x)
  tightest_prefix(x, s)


  0 <= offset < len(t) => xy = t &
                          len(x) = offset &
                          (-1 = indexof(y, s, 0) => -1 = i) &
                          (indexof(y, s, 0) >= 0 => indexof(t, s, 0) + offset = i)

  offset < 0 => i = -1

  optional lemmas:
   (len(s) > len(t)  -> i = -1)
   (len(s) <= len(t) -> i <= len(t)-len(s))
*/
void seq_axioms::add_indexof_axiom(expr* i) {
    expr* s = nullptr, *t = nullptr, *offset = nullptr;
    rational r;
    VERIFY(seq.str.is_index(i, t, s) ||
           seq.str.is_index(i, t, s, offset));
    expr_ref minus_one(a.mk_int(-1), m);
    expr_ref zero(a.mk_int(0), m);
    expr_ref xsy(m);
    
    literal cnt = mk_literal(seq.str.mk_contains(t, s));
    literal i_eq_m1 = mk_eq(i, minus_one);
    literal i_eq_0 = mk_eq(i, zero);
    literal s_eq_empty = mk_eq_empty(s);
    literal t_eq_empty = mk_eq_empty(t);

    // |t| = 0 => |s| = 0 or indexof(t,s,offset) = -1
    // ~contains(t,s) <=> indexof(t,s,offset) = -1

    add_axiom(cnt,  i_eq_m1);
    add_axiom(~t_eq_empty, s_eq_empty, i_eq_m1);

    if (!offset || (a.is_numeral(offset, r) && r.is_zero())) {
        expr_ref x  = m_sk.mk_indexof_left(t, s);
        expr_ref y  = m_sk.mk_indexof_right(t, s);
        xsy         = mk_concat(x, s, y);
        expr_ref lenx = mk_len(x);
        // |s| = 0 => indexof(t,s,0) = 0
        // contains(t,s) & |s| != 0 => t = xsy & indexof(t,s,0) = |x|
        add_axiom(~s_eq_empty, i_eq_0);
        add_axiom(~cnt, s_eq_empty, mk_seq_eq(t, xsy));
        add_axiom(~cnt, s_eq_empty, mk_eq(i, lenx));
        add_axiom(~cnt, mk_literal(a.mk_ge(i, zero)));
        tightest_prefix(s, x);
    }
    else {
        // offset >= len(t) => |s| = 0 or indexof(t, s, offset) = -1
        // offset > len(t) => indexof(t, s, offset) = -1
        // offset = len(t) & |s| = 0 => indexof(t, s, offset) = offset
        expr_ref len_t = mk_len(t);
        literal offset_ge_len = mk_literal(a.mk_ge(mk_sub(offset, len_t), zero));
        literal offset_le_len = mk_literal(a.mk_le(mk_sub(offset, len_t), zero));
        literal i_eq_offset = mk_eq(i, offset);
        add_axiom(~offset_ge_len, s_eq_empty, i_eq_m1);
        add_axiom(offset_le_len, i_eq_m1);
        add_axiom(~offset_ge_len, ~offset_le_len, ~s_eq_empty, i_eq_offset);

        expr_ref x = m_sk.mk_indexof_left(t, s, offset);
        expr_ref y = m_sk.mk_indexof_right(t, s, offset);
        expr_ref indexof0(seq.str.mk_index(y, s, zero), m);
        expr_ref offset_p_indexof0(a.mk_add(offset, indexof0), m);
        literal offset_ge_0 = mk_literal(a.mk_ge(offset, zero));

        // 0 <= offset & offset < len(t) => t = xy
        // 0 <= offset & offset < len(t) => len(x) = offset
        // 0 <= offset & offset < len(t) & indexof(y,s,0) = -1 => -1 = i
        // 0 <= offset & offset < len(t) & indexof(y,s,0) >= 0 =>
        //                  -1 = indexof(y,s,0) + offset = indexof(t, s, offset)

        add_axiom(~offset_ge_0, offset_ge_len, mk_seq_eq(t, mk_concat(x, y)));
        add_axiom(~offset_ge_0, offset_ge_len, mk_eq(mk_len(x), offset));
        add_axiom(~offset_ge_0, offset_ge_len,
                  ~mk_eq(indexof0, minus_one), i_eq_m1);
        add_axiom(~offset_ge_0, offset_ge_len,
                  ~mk_literal(a.mk_ge(indexof0, zero)),
                  mk_eq(offset_p_indexof0, i));

        // offset < 0 => -1 = i        
        add_axiom(offset_ge_0, i_eq_m1);
    }
}

/**

  !contains(t, s) => i = -1   
  |t| = 0 => |s| = 0 or i = -1
  |t| = 0 & |s| = 0 => i = 0
  |t| != 0 & contains(t, s) => t = xsy & i = len(x) 
  |s| = 0 or s = s_head*s_tail
  |s| = 0 or !contains(s_tail*y, s)

 */
void seq_axioms::add_last_indexof_axiom(expr* i) {
    expr* s = nullptr, *t = nullptr;
    VERIFY(seq.str.is_last_index(i, t, s));
    expr_ref minus_one(a.mk_int(-1), m);
    expr_ref zero(a.mk_int(0), m);
    expr_ref s_head(m), s_tail(m);
    expr_ref x  = m_sk.mk_last_indexof_left(t, s);
    expr_ref y  = m_sk.mk_last_indexof_right(t, s);
    m_sk.decompose(s, s_head, s_tail);
    literal cnt  = mk_literal(seq.str.mk_contains(t, s));
    literal cnt2 = mk_literal(seq.str.mk_contains(mk_concat(s_tail, y), s));
    literal i_eq_m1 = mk_eq(i, minus_one);
    literal i_eq_0  = mk_eq(i, zero);
    literal s_eq_empty = mk_eq_empty(s);
    literal t_eq_empty = mk_eq_empty(t);
    expr_ref xsy       = mk_concat(x, s, y);

    add_axiom(cnt, i_eq_m1);
    add_axiom(~t_eq_empty, s_eq_empty, i_eq_m1);
    add_axiom(~t_eq_empty, ~s_eq_empty, i_eq_0);
    add_axiom(t_eq_empty, ~cnt, mk_seq_eq(t, xsy));
    add_axiom(t_eq_empty, ~cnt, mk_eq(i, mk_len(x)));
    add_axiom(s_eq_empty, mk_eq(s, mk_concat(s_head, s_tail)));
    add_axiom(s_eq_empty, ~cnt2);
}

/*
  let r = replace(a, s, t)

  a = "" => s = "" or r = a
  contains(a, s) or r = a
  s = "" => r = t+a
  
  tightest_prefix(s, x)
  (contains(a, s) -> r = xty & a = xsy) &
  (!contains(a, s) -> r = a)

*/
void seq_axioms::add_replace_axiom(expr* r) {
    expr* u = nullptr, *s = nullptr, *t = nullptr;
    VERIFY(seq.str.is_replace(r, u, s, t));
    expr_ref x  = m_sk.mk_indexof_left(u, s);
    expr_ref y  = m_sk.mk_indexof_right(u, s);
    expr_ref xty = mk_concat(x, t, y);
    expr_ref xsy = mk_concat(x, s, y);
    literal a_emp = mk_eq_empty(u, true);
    literal s_emp = mk_eq_empty(u, true);
    literal cnt = mk_literal(seq.str.mk_contains(u, s));
    add_axiom(~a_emp, s_emp, mk_seq_eq(r, u));
    add_axiom(cnt,  mk_seq_eq(r, u));
    add_axiom(~s_emp, mk_seq_eq(r, mk_concat(t, u)));
    add_axiom(~cnt, a_emp, s_emp, mk_seq_eq(u, xsy));
    add_axiom(~cnt, a_emp, s_emp, mk_seq_eq(r, xty));
    ctx().force_phase(cnt);
    tightest_prefix(s, x);
}


/*
   let e = at(s, i)

   0 <= i < len(s) -> s = xey & len(x) = i & len(e) = 1
   i < 0 \/ i >= len(s) -> e = empty

*/
void seq_axioms::add_at_axiom(expr* e) {
    TRACE("seq", tout << "at-axiom: " << ctx().get_scope_level() << " " << mk_bounded_pp(e, m) << "\n";);
    expr* s = nullptr, *i = nullptr;
    VERIFY(seq.str.is_at(e, s, i));
    expr_ref zero(a.mk_int(0), m);
    expr_ref one(a.mk_int(1), m);
    expr_ref emp(seq.str.mk_empty(m.get_sort(e)), m);
    expr_ref len_s = mk_len(s);
    literal i_ge_0 = mk_literal(a.mk_ge(i, zero));
    literal i_ge_len_s = mk_literal(a.mk_ge(mk_sub(i, mk_len(s)), zero));
    expr_ref len_e = mk_len(e);

    rational iv;
    if (a.is_numeral(i, iv) && iv.is_unsigned()) {
        expr_ref_vector es(m);
        expr_ref nth(m);
        unsigned k = iv.get_unsigned();
        for (unsigned j = 0; j <= k; ++j) {
            es.push_back(seq.str.mk_unit(mk_nth(s, a.mk_int(j))));
        }
        nth = es.back();
        es.push_back(m_sk.mk_tail(s, i));
        add_axiom(~i_ge_0, i_ge_len_s, mk_seq_eq(s, seq.str.mk_concat(es)));
        add_axiom(~i_ge_0, i_ge_len_s, mk_seq_eq(nth, e));                
    }
    else {
        expr_ref x =     m_sk.mk_pre(s, i);
        expr_ref y =     m_sk.mk_tail(s, i);
        expr_ref xey   = mk_concat(x, e, y);
        expr_ref len_x = mk_len(x);
        add_axiom(~i_ge_0, i_ge_len_s, mk_seq_eq(s, xey));
        add_axiom(~i_ge_0, i_ge_len_s, mk_eq(i, len_x));
    }

    add_axiom(i_ge_0, mk_eq(e, emp));
    add_axiom(~i_ge_len_s, mk_eq(e, emp));
    add_axiom(~i_ge_0, i_ge_len_s, mk_eq(one, len_e));
    add_axiom(mk_literal(a.mk_le(len_e, one)));
}

/**
   i >= 0 i < len(s) => unit(nth_i(s, i)) = at(s, i)
   nth_i(unit(nth_i(s, i)), 0) = nth_i(s, i)
*/

void seq_axioms::add_nth_axiom(expr* e) {
    expr* s = nullptr, *i = nullptr;
    rational n;
    zstring str;
    VERIFY(seq.str.is_nth_i(e, s, i));
    if (seq.str.is_string(s, str) && a.is_numeral(i, n) && 
        n.is_unsigned() && n.get_unsigned() < str.length()) {
        app_ref ch(seq.str.mk_char(str[n.get_unsigned()]), m);
        add_axiom(mk_eq(ch, e));
    }
    else {
        expr_ref zero(a.mk_int(0), m);
        literal i_ge_0 =     mk_literal(a.mk_ge(i, zero));
        literal i_ge_len_s = mk_literal(a.mk_ge(mk_sub(i, mk_len(s)), zero));
        // at(s,i) = [nth(s,i)]
        expr_ref rhs(s, m);
        expr_ref lhs(seq.str.mk_unit(e), m);
        if (!seq.str.is_at(s) || zero != i) rhs = seq.str.mk_at(s, i);
        m_rewrite(rhs);
        add_axiom(~i_ge_0, i_ge_len_s, mk_eq(lhs, rhs));
    }
}


void seq_axioms::add_itos_axiom(expr* e) {
    expr* n = nullptr;
    TRACE("seq", tout << mk_pp(e, m) << "\n";);
    VERIFY(seq.str.is_itos(e, n));

    // itos(n) = "" <=> n < 0
    expr_ref zero(a.mk_int(0), m);
    literal eq1 = mk_literal(seq.str.mk_is_empty(e));
    literal ge0 = mk_literal(a.mk_ge(n, zero));
    // n >= 0 => itos(n) != ""
    // itos(n) = "" or n >= 0
    add_axiom(~eq1, ~ge0);
    add_axiom(eq1, ge0);
    add_axiom(mk_literal(a.mk_ge(mk_len(e), zero)));    
    
    // n >= 0 => stoi(itos(n)) = n
    app_ref stoi(seq.str.mk_stoi(e), m);
    add_axiom(~ge0, th.mk_preferred_eq(stoi, n));

    // itos(n) does not start with "0" when n > 0
    // n = 0 or at(itos(n),0) != "0"
    // alternative: n >= 0 => itos(stoi(itos(n))) = itos(n)
    expr_ref zs(seq.str.mk_string(symbol("0")), m);
    m_rewrite(zs);
    literal eq0 = mk_eq(n, zero);
    literal at0 = mk_eq(seq.str.mk_at(e, zero), zs);
    add_axiom(eq0, ~at0);
    add_axiom(~eq0, mk_eq(e, zs));
}

/**
   stoi(s) >= -1
   stoi("") = -1
*/
void seq_axioms::add_stoi_axiom(expr* e) {
    TRACE("seq", tout << mk_pp(e, m) << "\n";);
    expr* s = nullptr;
    VERIFY (seq.str.is_stoi(e, s));    
    add_axiom(mk_literal(a.mk_ge(e, a.mk_int(-1))));
    add_axiom(~mk_literal(seq.str.mk_is_empty(s)), mk_eq(seq.str.mk_stoi(s), a.mk_int(-1)));   
}

/**
   e1 < e2 => prefix(e1, e2) or e1 = xcy e1 < e2 => prefix(e1, e2) or
   c < d e1 < e2 => prefix(e1, e2) or e2 = xdz e1 < e2 => e1 != e2
   !(e1 < e2) => prefix(e2, e1) or e2 = xdz !(e1 < e2) => prefix(e2,
   e1) or d < c !(e1 < e2) => prefix(e2, e1) or e1 = xcy !(e1 = e2) or
   !(e1 < e2) optional: e1 < e2 or e1 = e2 or e2 < e1 !(e1 = e2) or
   !(e2 < e1) !(e1 < e2) or !(e2 < e1)
 */
void seq_axioms::add_lt_axiom(expr* n) {
    expr* e1 = nullptr, *e2 = nullptr;
    VERIFY(seq.str.is_lt(n, e1, e2));
    sort* s = m.get_sort(e1);
    sort* char_sort = nullptr;
    VERIFY(seq.is_seq(s, char_sort));
    literal lt = mk_literal(n);
    expr_ref x = m_sk.mk(symbol("str.lt.x"), e1, e2);
    expr_ref y = m_sk.mk(symbol("str.lt.y"), e1, e2);
    expr_ref z = m_sk.mk(symbol("str.lt.z"), e1, e2);
    expr_ref c = m_sk.mk(symbol("str.lt.c"), e1, e2, char_sort);
    expr_ref d = m_sk.mk(symbol("str.lt.d"), e1, e2, char_sort);
    expr_ref xcy = mk_concat(x, seq.str.mk_unit(c), y);
    expr_ref xdz = mk_concat(x, seq.str.mk_unit(d), z);
    literal eq   = mk_eq(e1, e2);
    literal pref21 = mk_literal(seq.str.mk_prefix(e2, e1));
    literal pref12 = mk_literal(seq.str.mk_prefix(e1, e2));
    literal e1xcy = mk_eq(e1, xcy);
    literal e2xdz = mk_eq(e2, xdz);
    literal ltcd = mk_literal(seq.mk_lt(c, d));
    literal ltdc = mk_literal(seq.mk_lt(d, c));
    add_axiom(~lt, pref12, e2xdz);
    add_axiom(~lt, pref12, e1xcy);
    add_axiom(~lt, pref12, ltcd);
    add_axiom(lt, pref21, e1xcy);
    add_axiom(lt, pref21, ltdc);
    add_axiom(lt, pref21, e2xdz);
    add_axiom(~eq, ~lt);
}

/**
   e1 <= e2 <=> e1 < e2 or e1 = e2
*/
void seq_axioms::add_le_axiom(expr* n) {
    expr* e1 = nullptr, *e2 = nullptr;
    VERIFY(seq.str.is_le(n, e1, e2));
    literal lt = mk_literal(seq.str.mk_lex_lt(e1, e2));
    literal le = mk_literal(n);
    literal eq = mk_eq(e1, e2);
    add_axiom(~le, lt, eq);
    add_axiom(~eq, le);
    add_axiom(~lt, le);
}

void seq_axioms::add_unit_axiom(expr* n) {
    expr* u = nullptr;
    VERIFY(seq.str.is_unit(n, u));
    add_axiom(mk_eq(u, m_sk.mk_unit_inv(n)));
}

