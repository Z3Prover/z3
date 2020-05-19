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
    m_sk(m, r),
    m_digits_initialized(false)
{}

literal seq_axioms::mk_eq(expr* a, expr* b) {
    return th.mk_eq(a, b, false);
}

expr_ref seq_axioms::mk_sub(expr* x, expr* y) {
    expr_ref result(a.mk_sub(x, y), m);
    m_rewrite(result);
    return result;
}

expr_ref seq_axioms::mk_len(expr* s) {
    expr_ref result(seq.str.mk_length(s), m); 
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

/***

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
    expr* _s = nullptr, *_i = nullptr, *_l = nullptr;
    VERIFY(seq.str.is_extract(e, _s, _i, _l));
    expr_ref s(_s, m), i(_i, m), l(_l, m);
    m_rewrite(s);
    m_rewrite(i);
    if (l) m_rewrite(l);
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

    literal i_ge_0    = mk_ge(i, 0);
    literal i_le_ls   = mk_le(mk_sub(i, ls), 0);
    literal ls_le_i   = mk_le(mk_sub(ls, i), 0);
    literal ls_ge_li  = mk_ge(ls_minus_i_l, 0);
    literal l_ge_0    = mk_ge(l, 0);
    literal l_le_0    = mk_le(l, 0);
    literal ls_le_0   = mk_le(ls, 0);
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
    literal l_ge_0 = mk_ge(l, 0);
    literal l_le_s = mk_le(mk_sub(l, ls), 0);
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
    literal i_ge_0 = mk_ge(i, 0);
    literal i_le_s = mk_le(mk_sub(i, ls), 0);
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
    expr* _s = nullptr, *_t = nullptr, *_offset = nullptr;
    rational r;
    VERIFY(seq.str.is_index(i, _t, _s) ||
           seq.str.is_index(i, _t, _s, _offset));
    expr_ref minus_one(a.mk_int(-1), m);
    expr_ref zero(a.mk_int(0), m);
    expr_ref xsy(m), t(_t, m), s(_s, m), offset(_offset, m);
    m_rewrite(t);
    m_rewrite(s);
    if (offset) m_rewrite(offset);
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
        add_axiom(~cnt, mk_ge(i, 0));
        tightest_prefix(s, x);
    }
    else {
        // offset >= len(t) => |s| = 0 or indexof(t, s, offset) = -1
        // offset > len(t) => indexof(t, s, offset) = -1
        // offset = len(t) & |s| = 0 => indexof(t, s, offset) = offset
        expr_ref len_t = mk_len(t);
        literal offset_ge_len = mk_ge(mk_sub(offset, len_t), 0);
        literal offset_le_len = mk_le(mk_sub(offset, len_t), 0);
        literal i_eq_offset = mk_eq(i, offset);
        add_axiom(~offset_ge_len, s_eq_empty, i_eq_m1);
        add_axiom(offset_le_len, i_eq_m1);
        add_axiom(~offset_ge_len, ~offset_le_len, ~s_eq_empty, i_eq_offset);

        expr_ref x = m_sk.mk_indexof_left(t, s, offset);
        expr_ref y = m_sk.mk_indexof_right(t, s, offset);
        expr_ref indexof0(seq.str.mk_index(y, s, zero), m);
        expr_ref offset_p_indexof0(a.mk_add(offset, indexof0), m);
        literal offset_ge_0 = mk_ge(offset, 0);

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
                  ~mk_ge(indexof0, 0),
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
    expr* _s = nullptr, *_t = nullptr;
    VERIFY(seq.str.is_last_index(i, _t, _s));
    expr_ref s(_s, m), t(_t, m);
    m_rewrite(s);
    m_rewrite(t);
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
  let r = replace(u, s, t)

  
  - if s is empty, the result is to prepend t to u; 
  - if s does not occur in u then the result is u.

  s = "" => r = t+u
  u = "" => s = "" or r = u
  ~contains(u,s) => r = u
  
  tightest_prefix(s, x)
  contains(u, s) => r = xty & u = xsy
  ~contains(u, s) => r = u

*/
void seq_axioms::add_replace_axiom(expr* r) {
    expr* _u = nullptr, *_s = nullptr, *_t = nullptr;
    VERIFY(seq.str.is_replace(r, _u, _s, _t));
    expr_ref u(_u, m), s(_s, m), t(_t, m);
    m_rewrite(u);
    m_rewrite(s);
    m_rewrite(t);
    expr_ref x  = m_sk.mk_indexof_left(u, s);
    expr_ref y  = m_sk.mk_indexof_right(u, s);
    expr_ref xty = mk_concat(x, t, y);
    expr_ref xsy = mk_concat(x, s, y);
    literal u_emp = mk_eq_empty(u, true);
    literal s_emp = mk_eq_empty(s, true);
    literal cnt = mk_literal(seq.str.mk_contains(u, s));
    add_axiom(~s_emp, mk_seq_eq(r, mk_concat(t, u)));
    add_axiom(~u_emp, s_emp, mk_seq_eq(r, u));
    add_axiom(cnt,  mk_seq_eq(r, u));
    add_axiom(~cnt, u_emp, s_emp, mk_seq_eq(u, xsy));
    add_axiom(~cnt, u_emp, s_emp, mk_seq_eq(r, xty));
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
    expr* _s = nullptr, *_i = nullptr;
    VERIFY(seq.str.is_at(e, _s, _i));
    expr_ref s(_s, m), i(_i, m);
    m_rewrite(s);
    m_rewrite(i);
    expr_ref zero(a.mk_int(0), m);
    expr_ref one(a.mk_int(1), m);
    expr_ref emp(seq.str.mk_empty(m.get_sort(e)), m);
    expr_ref len_s = mk_len(s);
    literal i_ge_0 = mk_ge(i, 0);
    literal i_ge_len_s = mk_ge(mk_sub(i, mk_len(s)), 0);
    expr_ref len_e = mk_len(e);

    rational iv;
    if (a.is_numeral(i, iv) && iv.is_unsigned()) {
        expr_ref_vector es(m);
        expr_ref nth(m);
        unsigned k = iv.get_unsigned();
        for (unsigned j = 0; j <= k; ++j) {
            es.push_back(seq.str.mk_unit(mk_nth(s, j)));
        }
        nth = es.back();
        es.push_back(m_sk.mk_tail(s, i));
        add_axiom(~i_ge_0, i_ge_len_s, mk_seq_eq(s, seq.str.mk_concat(es, m.get_sort(e))));
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
    add_axiom(mk_le(len_e, 1));
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
        literal i_ge_0 =     mk_ge(i, 0);
        literal i_ge_len_s = mk_ge(mk_sub(i, mk_len(s)), 0);
        // at(s,i) = [nth(s,i)]
        expr_ref rhs(s, m);
        expr_ref lhs(seq.str.mk_unit(e), m);
        if (!seq.str.is_at(s) || zero != i) rhs = seq.str.mk_at(s, i);
        m_rewrite(rhs);
        add_axiom(~i_ge_0, i_ge_len_s, mk_eq(lhs, rhs));
    }
}


void seq_axioms::add_itos_axiom(expr* e) {
    expr* _n = nullptr;
    TRACE("seq", tout << mk_pp(e, m) << "\n";);
    VERIFY(seq.str.is_itos(e, _n));
    expr_ref n(_n, m);
    m_rewrite(n);

    // itos(n) = "" <=> n < 0
    expr_ref zero(a.mk_int(0), m);
    literal eq1 = mk_literal(seq.str.mk_is_empty(e));
    literal ge0 = mk_ge(n, 0);
    // n >= 0 => itos(n) != ""
    // itos(n) = "" or n >= 0
    add_axiom(~eq1, ~ge0);
    add_axiom(eq1, ge0);
    add_axiom(mk_ge(mk_len(e), 0));
    
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
   stoi(s) >= 0 => is_digit(nth(s,0))
*/
void seq_axioms::add_stoi_axiom(expr* e) {
    TRACE("seq", tout << mk_pp(e, m) << "\n";);
    literal ge0 = mk_ge(e, 0);      
    expr* s = nullptr;
    VERIFY (seq.str.is_stoi(e, s));    
    add_axiom(mk_ge(e, -1));                             // stoi(s) >= -1
    add_axiom(~mk_eq_empty(s), mk_eq(e, a.mk_int(-1)));  // s = "" => stoi(s) = -1
    add_axiom(~ge0, is_digit(mk_nth(s, 0)));             // stoi(s) >= 0 => is_digit(nth(s,0))

}

/**

   len(s) <= k => stoi(s) = stoi(s, k)
   len(s) > 0,  is_digit(nth(s,0)) => stoi(s, 0) = digit(nth_i(s, 0))
   len(s) > 0, ~is_digit(nth(s,0)) => stoi(s, 0) = -1

   0 < i, len(s) <= i =>        stoi(s, i) = stoi(s, i - 1)
   0 < i, len(s) > i, stoi(s, i - 1) >= 0, is_digit(nth(s, i - 1)) => stoi(s, i) = 10*stoi(s, i - 1) + digit(nth_i(s, i - 1))   
   0 < i, len(s) > i, stoi(s, i - 1) < 0       => stoi(s, i) = -1
   0 < i, len(s) > i, ~is_digit(nth(s, i - 1)) => stoi(s, i) = -1

                                

Define auxiliary function with the property:
   for 0 <= i < k
     stoi(s, i) := stoi(extract(s, 0, i+1)) 

   for 0 < i < k:
     len(s) > i  => stoi(s, i) := stoi(extract(s, 0, i))*10 + stoi(extract(s, i, 1))
     len(s) <= i => stoi(s, i) := stoi(extract(s, 0, i-1), i-1)

   for i <= i < k:
     stoi(s) > = 0, len(s) > i => is_digit(nth(s, i))     

 */
void seq_axioms::add_stoi_axiom(expr* e, unsigned k) {
    SASSERT(k > 0);
    expr* _s = nullptr;
    VERIFY (seq.str.is_stoi(e, _s));
    expr_ref s(_s, m);
    m_rewrite(s);
    auto stoi2 = [&](unsigned j) { return m_sk.mk("seq.stoi", s, a.mk_int(j), a.mk_int()); }; 
    auto digit = [&](unsigned j) { return m_sk.mk_digit2int(mk_nth(s, j)); };
    auto is_digit_ = [&](unsigned j) { return is_digit(mk_nth(s, j)); };
    expr_ref len = mk_len(s);
    literal ge0 = mk_ge(e, 0);
    literal lek = mk_le(len, k);
    add_axiom(~lek, mk_eq(e, stoi2(k-1)));                                    // len(s) <= k  => stoi(s) = stoi(s, k-1)
    add_axiom(mk_le(len, 0), ~is_digit_(0), mk_eq(stoi2(0), digit(0)));       // len(s) > 0, is_digit(nth(s, 0)) => stoi(s,0) = digit(s,0)
    add_axiom(mk_le(len, 0), is_digit_(0),  mk_eq(stoi2(0), a.mk_int(-1)));   // len(s) > 0, ~is_digit(nth(s, 0)) => stoi(s,0) = -1
    for (unsigned i = 1; i < k; ++i) {

        // len(s) <= i => stoi(s, i) = stoi(s, i - 1)

        add_axiom(~mk_le(len, i),  mk_eq(stoi2(i), stoi2(i-1)));

        // len(s) > i, stoi(s, i - 1) >= 0, is_digit(nth(s, i)) => stoi(s, i) = 10*stoi(s, i - 1) + digit(i)
        // len(s) > i, stoi(s, i - 1) < 0 => stoi(s, i) = -1
        // len(s) > i, ~is_digit(nth(s, i)) => stoi(s, i) = -1

        add_axiom(mk_le(len, i), ~mk_ge(stoi2(i-1), 0), ~is_digit_(i), mk_eq(stoi2(i), a.mk_add(a.mk_mul(a.mk_int(10), stoi2(i-1)), digit(i))));
        add_axiom(mk_le(len, i), is_digit_(i),                         mk_eq(stoi2(i), a.mk_int(-1)));
        add_axiom(mk_le(len, i), mk_ge(stoi2(i-1), 0),                 mk_eq(stoi2(i), a.mk_int(-1)));

        // stoi(s) >= 0, i < len(s) => is_digit(nth(s, i))

        add_axiom(~ge0, mk_le(len, i), is_digit_(i));
    }
}

/**
   Let s := itos(e)

   Relate values of e with len(s) where len(s) is bounded by k.

   |s| = 0 => e < 0

   |s| <= 1 => e < 10
   |s| <= 2 => e < 100
   |s| <= 3 => e < 1000

   |s| >= 1 => e >= 0
   |s| >= 2 => e >= 10
   |s| >= 3 => e >= 100

   There are no constraints to ensure that the string itos(e) 
   contains the valid digits corresponding to e >= 0.
   The validity of itos(e) is ensured by the following property:
   e is either of the form stoi(s) for some s, or there is a term
   stoi(itos(e)) and axiom e >= 0 => stoi(itos(e)) = e.
   Then the axioms for stoi(itos(e)) ensure that the characters of
   itos(e) are valid digits and the axiom stoi(itos(e)) = e ensures 
   these digits encode e.
   The option of constraining itos(e) digits directly does not
   seem appealing becaues it requires an order of quadratic number
   of constraints for all possible lengths of itos(e) (e.g, log_10(e)).

*/

void seq_axioms::add_itos_axiom(expr* s, unsigned k) {
    expr* e = nullptr;
    VERIFY(seq.str.is_itos(s, e));
    expr_ref len = mk_len(s);
    add_axiom(mk_ge(e, 10), mk_le(len, 1));
    add_axiom(mk_le(e, -1), mk_ge(len, 1));
    rational lo(1);
    for (unsigned i = 1; i <= k; ++i) {
        lo *= rational(10);
        add_axiom(mk_ge(e, lo), mk_le(len, i));
        add_axiom(mk_le(e, lo - 1), mk_ge(len, i + 1));
    }
}

literal seq_axioms::is_digit(expr* ch) {
    ensure_digit_axiom();
    literal isd = mk_literal(m_sk.mk_is_digit(ch));
    expr_ref d2i = m_sk.mk_digit2int(ch);
    expr_ref _lo(seq.mk_le(seq.mk_char('0'), ch), m);
    expr_ref _hi(seq.mk_le(ch, seq.mk_char('9')), m);
    literal lo = mk_literal(_lo);
    literal hi = mk_literal(_hi);
    add_axiom(~lo, ~hi, isd);
    add_axiom(~isd, lo);
    add_axiom(~isd, hi);
    return isd;
}

/**
   Bridge character digits to integers.
*/

void seq_axioms::ensure_digit_axiom() {
    if (!m_digits_initialized) {
        for (unsigned i = 0; i < 10; ++i) {
            expr_ref cnst(seq.mk_char('0'+i), m);
            add_axiom(mk_eq(m_sk.mk_digit2int(cnst), a.mk_int(i)));
        }
        ctx().push_trail(value_trail<context, bool>(m_digits_initialized));
        m_digits_initialized = true;
    }
}


/**
   e1 < e2 => prefix(e1, e2) or e1 = xcy 
   e1 < e2 => prefix(e1, e2) or c < d 
   e1 < e2 => prefix(e1, e2) or e2 = xdz 
   e1 < e2 => e1 != e2
   !(e1 < e2) => prefix(e2, e1) or e2 = xdz 
   !(e1 < e2) => prefix(e2, e1) or d < c 
   !(e1 < e2) => prefix(e2, e1) or e1 = xcy 
   !(e1 = e2) or !(e1 < e2) 

   optional: 
   e1 < e2 or e1 = e2 or e2 < e1 
   !(e1 = e2) or !(e2 < e1) 
   !(e1 < e2) or !(e2 < e1)
 */
void seq_axioms::add_lt_axiom(expr* n) {
    expr* _e1 = nullptr, *_e2 = nullptr;
    VERIFY(seq.str.is_lt(n, _e1, _e2));
    expr_ref e1(_e1, m), e2(_e2, m);
    m_rewrite(e1);
    m_rewrite(e2);
    sort* s = m.get_sort(e1);
    sort* char_sort = nullptr;
    VERIFY(seq.is_seq(s, char_sort));
    literal lt = mk_literal(n);
    expr_ref x = m_sk.mk("str.<.x", e1, e2);
    expr_ref y = m_sk.mk("str.<.y", e1, e2);
    expr_ref z = m_sk.mk("str.<.z", e1, e2);
    expr_ref c = m_sk.mk("str.<.c", e1, e2, char_sort);
    expr_ref d = m_sk.mk("str.<.d", e1, e2, char_sort);
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

/**
   is_digit(e) <=> to_code('0') <= to_code(e) <= to_code('9')
 */
void seq_axioms::add_is_digit_axiom(expr* n) {
    expr* e = nullptr;
    VERIFY(seq.str.is_is_digit(n, e)); 
    literal is_digit = mk_literal(n);
    expr_ref to_code(seq.str.mk_to_code(e), m);
    literal ge0 = mk_ge(to_code, (unsigned)'0');
    literal le9 = mk_le(to_code, (unsigned)'9');
    add_axiom(~is_digit, ge0);
    add_axiom(~is_digit, le9);
    add_axiom(is_digit, ~ge0, ~le9);
}

/**
   len(e) = 1 => 0 <= to_code(e) <= max_code
   len(e) != 1 => to_code(e) = -1
 */
void seq_axioms::add_str_to_code_axiom(expr* n) {
    expr* e = nullptr;
    VERIFY(seq.str.is_to_code(n, e)); 
    literal len_is1 = mk_eq(mk_len(e), a.mk_int(1));
    add_axiom(~len_is1, mk_ge(n, 0)); 
    add_axiom(~len_is1, mk_le(n, zstring::max_char()));
    add_axiom(len_is1, mk_eq(n, a.mk_int(-1)));
}

/**
   0 <= e <= max_char => len(from_code(e)) = 1
   0 <= e <= max_char => to_code(from_code(e)) = e
   e < 0 or e > max_char => len(from_code(e)) = ""
 */
void seq_axioms::add_str_from_code_axiom(expr* n) {
    expr* e = nullptr;
    VERIFY(seq.str.is_from_code(n, e)); 
    literal ge = mk_ge(e, 0);
    literal le = mk_le(e, zstring::max_char());
    literal emp = mk_literal(seq.str.mk_is_empty(n));
    add_axiom(~ge, ~le, mk_eq(mk_len(n), a.mk_int(1)));
    add_axiom(~ge, ~le, mk_eq(seq.str.mk_to_code(n), e));
    add_axiom(ge, emp);
    add_axiom(le, emp);
}


/**
Unit is injective:

   u = inv-unit(unit(u)) 
*/

void seq_axioms::add_unit_axiom(expr* n) {
    expr* u = nullptr;
    VERIFY(seq.str.is_unit(n, u));
    add_axiom(mk_eq(u, m_sk.mk_unit_inv(n)));
}

/**

 suffix(s, t) => s = seq.suffix_inv(s, t) + t
~suffix(s, t) => len(s) > len(t) or s = y(s, t) + unit(c(s, t)) + x(s, t)
~suffix(s, t) => len(s) > len(t) or t = z(s, t) + unit(d(s, t)) + x(s, t)
~suffix(s, t) => len(s) > len(t) or c(s,t) != d(s,t)

*/

void seq_axioms::add_suffix_axiom(expr* e) {
    expr* _s = nullptr, *_t = nullptr;
    VERIFY(seq.str.is_suffix(e, _s, _t));
    expr_ref s(_s, m), t(_t, m);
    m_rewrite(s);
    m_rewrite(t);
    literal lit = mk_literal(e);
    literal s_gt_t = mk_ge(mk_sub(mk_len(s), mk_len(t)), 1);
    sort* char_sort = nullptr;
    VERIFY(seq.is_seq(m.get_sort(s), char_sort));
    expr_ref x = m_sk.mk("seq.suffix.x", s, t);
    expr_ref y = m_sk.mk("seq.suffix.y", s, t);
    expr_ref z = m_sk.mk("seq.suffix.z", s, t);
    expr_ref c = m_sk.mk("seq.suffix.c", s, t, char_sort);
    expr_ref d = m_sk.mk("seq.suffix.d", s, t, char_sort);
    add_axiom(lit, s_gt_t, mk_seq_eq(s, mk_concat(y, seq.str.mk_unit(c), x)));
    add_axiom(lit, s_gt_t, mk_seq_eq(t, mk_concat(z, seq.str.mk_unit(d), x)));
    add_axiom(lit, s_gt_t, ~mk_eq(c, d));
}

void seq_axioms::add_prefix_axiom(expr* e) {
    expr* _s = nullptr, *_t = nullptr;
    VERIFY(seq.str.is_prefix(e, _s, _t));
    expr_ref s(_s, m), t(_t, m);
    m_rewrite(s);
    m_rewrite(t);
    literal lit = mk_literal(e);
    literal s_gt_t = mk_ge(mk_sub(mk_len(s), mk_len(t)), 1);
    sort* char_sort = nullptr;
    VERIFY(seq.is_seq(m.get_sort(s), char_sort));
    expr_ref x = m_sk.mk("seq.prefix.x", s, t);
    expr_ref y = m_sk.mk("seq.prefix.y", s, t);
    expr_ref z = m_sk.mk("seq.prefix.z", s, t);
    expr_ref c = m_sk.mk("seq.prefix.c", s, t, char_sort);
    expr_ref d = m_sk.mk("seq.prefix.d", s, t, char_sort);
    add_axiom(lit, s_gt_t, mk_seq_eq(s, mk_concat(x, seq.str.mk_unit(c), y)));
    add_axiom(lit, s_gt_t, mk_seq_eq(t, mk_concat(x, seq.str.mk_unit(d), z)), mk_seq_eq(t, x));
    add_axiom(lit, s_gt_t, ~mk_eq(c, d));
}

/***
    let n = len(x)
    - len(a ++ b) = len(a) + len(b) if x = a ++ b
    - len(unit(u)) = 1              if x = unit(u)
    - len(str) = str.length()       if x = str
    - len(empty) = 0                if x = empty
    - len(int.to.str(i)) >= 1       if x = int.to.str(i) and more generally if i = 0 then 1 else 1+floor(log(|i|))
    - len(x) >= 0                   otherwise
 */
void seq_axioms::add_length_axiom(expr* n) {
    expr* x = nullptr;
    VERIFY(seq.str.is_length(n, x));
    if (seq.str.is_concat(x) ||
        seq.str.is_unit(x) ||
        seq.str.is_empty(x) ||
        seq.str.is_string(x)) {
        expr_ref len(n, m);
        m_rewrite(len);
        SASSERT(n != len);
        add_axiom(mk_eq(len, n));
    }
    else {
        add_axiom(mk_ge(n, 0));
    }
}

/**
   ~contains(a, b) => ~prefix(b, a)
   ~contains(a, b) => ~contains(tail(a), b) or a = empty
   ~contains(a, b) & a = empty => b != empty
   ~(a = empty) => a = head + tail 
 */
void seq_axioms::unroll_not_contains(expr* e) {
    expr_ref head(m), tail(m);
    expr* a = nullptr, *b = nullptr;
    VERIFY(seq.str.is_contains(e, a, b));
    m_sk.decompose(a, head, tail);
    expr_ref pref(seq.str.mk_prefix(b, a), m);
    expr_ref postf(seq.str.mk_contains(tail, b), m);
    m_rewrite(pref);
    m_rewrite(postf);
    literal pre = mk_literal(pref);
    literal cnt = mk_literal(e);
    literal ctail = mk_literal(postf);
    literal emp = mk_eq_empty(a, true);
    add_axiom(cnt, ~pre);
    add_axiom(cnt, ~ctail);
    add_axiom(~emp, mk_eq_empty(tail));
    add_axiom(emp, mk_eq(a, seq.str.mk_concat(head, tail)));
}


expr_ref seq_axioms::add_length_limit(expr* s, unsigned k) {
    expr_ref bound_tracker  = m_sk.mk_length_limit(s, k);
    expr* s0 = nullptr;
    if (seq.str.is_stoi(s, s0)) 
        s = s0; 
    literal bound_predicate = mk_le(mk_len(s), k);
    add_axiom(~mk_literal(bound_tracker), bound_predicate);
    return bound_tracker;
}
