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
#include "ast/rewriter/seq_axioms.h"

namespace seq {

    axioms::axioms(th_rewriter& r):
        m(r.m()),
        m_rewrite(r),
        a(m),
        seq(m),
        m_sk(m, r),
        m_clause(m),
        m_trail(m)
    {}
        
    expr_ref axioms::mk_sub(expr* x, expr* y) {
        expr_ref result(a.mk_sub(x, y), m);
        m_rewrite(result);
        return result;
    }

    expr_ref axioms::mk_ge_e(expr* x, expr* y) {
        expr_ref ge(a.mk_ge(x, y), m);
        m_rewrite(ge);
        return ge;
    }

    expr_ref axioms::mk_le_e(expr* x, expr* y) {
        expr_ref le(a.mk_le(x, y), m);
        m_rewrite(le);
        return le;
    }

    expr_ref axioms::mk_seq_eq(expr* a, expr* b) { 
        SASSERT(seq.is_seq(a) && seq.is_seq(b)); 
        expr_ref result(m_sk.mk_eq(a, b), m);
        m_set_phase(result);
        return result;
    }

    /**
     * Create a special equality predicate for sequences.
     * The sequence solver ignores the predicate when it
     * is assigned to false. If the predicate is assigned
     * to true it enforces the equality.
     * 
     * This is intended to save the solver from satisfying disequality
     * constraints that are not relevant. The use of this predicate
     * needs some care because it can lead to incompleteness.
     * The clauses where this predicate are used have to ensure
     * that whenever it is assigned false, the clause
     * is satisfied by a solution where the equality is either false
     * or irrelevant. 
     */
    expr_ref axioms::mk_eq_empty(expr* e) { 
        return mk_seq_eq(seq.str.mk_empty(e->get_sort()), e);
    }

    expr_ref axioms::purify(expr* e) { 
        if (!e)
            return expr_ref(m);
        if (get_depth(e) == 1)
            return expr_ref(e, m);
        if (m.is_value(e))
            return expr_ref(e, m);

        expr_ref p(e, m);
        m_rewrite(p);
        if (p == e)
            return p;

        expr* r = nullptr;
        if (m_purified.find(e, r)) 
            p = r;
        else {
            gc_purify();
            p = expr_ref(m.mk_fresh_const("seq.purify", e->get_sort()), m);
            m_purified.insert(e, p);
            m_trail.push_back(e);
            m_trail.push_back(p);
        }
        add_clause(mk_eq(p, e));
        return expr_ref(p, m);
    }

    void axioms::gc_purify() {
        if (m_trail.size() != 4000)
            return;
        unsigned new_size = 2000;
        expr_ref_vector new_trail(m, new_size, m_trail.data() + new_size);
        m_purified.reset();
        for (unsigned i = 0; i < new_size; i += 2) 
            m_purified.insert(new_trail.get(i), new_trail.get(i + 1));
        m_trail.reset();
        m_trail.append(new_trail);
    }
    
    expr_ref axioms::mk_len(expr* s) {
        expr_ref result(seq.str.mk_length(s), m); 
        m_rewrite(result);
        return result;
    }

    void axioms::add_clause(expr_ref const& a) {
        m_clause.reset();
        m_clause.push_back(a);
        m_add_clause(m_clause);
    }

    void axioms::add_clause(expr_ref const& a, expr_ref const& b) {
        m_clause.reset();
        m_clause.push_back(a);
        m_clause.push_back(b);
        m_add_clause(m_clause);
    }

    void axioms::add_clause(expr_ref const& a, expr_ref const& b, expr_ref const& c) {
        m_clause.reset();
        m_clause.push_back(a);
        m_clause.push_back(b);
        m_clause.push_back(c);
        m_add_clause(m_clause);
    }

    void axioms::add_clause(expr_ref const& a, expr_ref const& b, expr_ref const& c, expr_ref const & d) {
        m_clause.reset();
        m_clause.push_back(a);
        m_clause.push_back(b);
        m_clause.push_back(c);
        m_clause.push_back(d);
        m_add_clause(m_clause);
    }

    void axioms::add_clause(expr_ref const& a, expr_ref const& b, expr_ref const& c, expr_ref const & d, expr_ref const& e) {
        m_clause.reset();
        m_clause.push_back(a);
        m_clause.push_back(b);
        m_clause.push_back(c);
        m_clause.push_back(d);
        m_clause.push_back(e);
        m_add_clause(m_clause);
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

    void axioms::extract_axiom(expr* e) {
        TRACE("seq", tout << mk_pp(e, m) << "\n";);
        expr* _s = nullptr, *_i = nullptr, *_l = nullptr;
        VERIFY(seq.str.is_extract(e, _s, _i, _l));
        auto s = purify(_s);
        auto i = purify(_i);
        auto l = purify(_l);
        if (small_segment_axiom(e, _s, _i, _l)) 
            return;

        if (is_tail(s, _i, _l)) {
            tail_axiom(e, s);
            return;
        }
        if (is_drop_last(s, _i, _l)) {
            drop_last_axiom(e, s);
            return;
        }
        if (is_extract_prefix(s, _i, _l)) {
            extract_prefix_axiom(e, s, l);
            return;
        }
        if (is_extract_suffix(s, _i, _l)) {
            extract_suffix_axiom(e, s, i);
            return;
        }
        TRACE("seq", tout << s << " " << i << " " << l << "\n";);
        expr_ref x = m_sk.mk_pre(s, i);
        expr_ref ls = mk_len(_s);
        expr_ref lx = mk_len(x);
        expr_ref le = mk_len(e);
        expr_ref ls_minus_i_l(mk_sub(mk_sub(ls, _i), _l), m);
        expr_ref y = m_sk.mk_post(s, a.mk_add(i, l));
        expr_ref xe = mk_concat(x, e);
        expr_ref xey = mk_concat(x, e, y);
        expr_ref zero(a.mk_int(0), m);

        expr_ref i_ge_0    = mk_ge(_i, 0);
        expr_ref i_le_ls   = mk_le(mk_sub(_i, ls), 0);
        expr_ref ls_le_i   = mk_le(mk_sub(ls, _i), 0);
        expr_ref ls_ge_li  = mk_ge(ls_minus_i_l, 0);
        expr_ref l_ge_0    = mk_ge(l, 0);
        expr_ref l_le_0    = mk_le(l, 0);
        expr_ref ls_le_0   = mk_le(ls, 0);
        expr_ref le_is_0   = mk_eq(le, zero);


        // 0 <= i & i <= |s| & 0 <= l => xey = s
        // 0 <= i & i <= |s| => |x| = i
        // 0 <= i & i <= |s| & l >= 0 & |s| >= l + i => |e| = l
        // 0 <= i & i <= |s| & |s| < l + i => |e| = |s| - i
        // i < 0 => |e| = 0
        // |s| <= i => |e| = 0
        // |s| <= 0 => |e| = 0
        // l <= 0 => |e| = 0
        // |e| = 0 & i >= 0 & |s| > i & |s| > 0 => l <= 0
        add_clause(~i_ge_0, ~i_le_ls, ~l_ge_0, mk_seq_eq(xey, s));
        add_clause(~i_ge_0, ~i_le_ls, mk_eq(lx, i));
        add_clause(~i_ge_0, ~i_le_ls, ~l_ge_0, ~ls_ge_li, mk_eq(le, l));
        add_clause(~i_ge_0, ~i_le_ls, ~l_ge_0, ls_ge_li, mk_eq(le, mk_sub(ls, i)));
        add_clause(i_ge_0,   le_is_0);
        add_clause(~ls_le_i, le_is_0);
        add_clause(~ls_le_0, le_is_0);
        add_clause(~l_le_0,  le_is_0);
        add_clause(~le_is_0, ~i_ge_0, ls_le_i, ls_le_0, l_le_0);
    }

    void axioms::tail_axiom(expr* e, expr* s) {    
        expr_ref head(m), tail(m);
        m_sk.decompose(s, head, tail);
        TRACE("seq", tout << "tail " << mk_bounded_pp(e, m, 2) << " " << mk_bounded_pp(s, m, 2) << "\n";);
        expr_ref emp = mk_eq_empty(s);
        add_clause(emp, mk_seq_eq(s, mk_concat(head, e)));
        add_clause(~emp, mk_eq_empty(e));
    }

    void axioms::drop_last_axiom(expr* e, expr* s) {
        TRACE("seq", tout << "drop last " << mk_bounded_pp(e, m, 2) << " " << mk_bounded_pp(s, m, 2) << "\n";);
        expr_ref emp = mk_eq_empty(s);
        add_clause(emp, mk_seq_eq(s, mk_concat(e, seq.str.mk_unit(m_sk.mk_last(s)))));
        add_clause(~emp, mk_eq_empty(e));
    }

    bool axioms::is_drop_last(expr* s, expr* i, expr* l) {
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

    bool axioms::small_segment_axiom(expr* s, expr* e, expr* i, expr* l) {
        rational ln;
        if (a.is_numeral(i, ln) && ln >= 0 && a.is_numeral(l, ln) && ln <= 5) {
            expr_ref_vector es(m);
            for (unsigned j = 0; j < ln; ++j) 
                es.push_back(seq.str.mk_at(e, a.mk_add(i, a.mk_int(j))));
            expr_ref r(seq.str.mk_concat(es, e->get_sort()), m);
            add_clause(mk_seq_eq(r, s));
            return true;
        }
        return false;
    }


    bool axioms::is_tail(expr* s, expr* i, expr* l) {
        rational i1;
        if (!a.is_numeral(i, i1) || !i1.is_one()) 
            return false;
        expr_ref l2(m), l1(l, m);
        l2 = mk_sub(mk_len(s), a.mk_int(1));
        m_rewrite(l1);
        m_rewrite(l2);
        return l1 == l2;
    }

    bool axioms::is_extract_prefix(expr* s, expr* i, expr* l) {
        rational i1;
        return a.is_numeral(i, i1) && i1.is_zero();    
    }

    bool axioms::is_extract_suffix(expr* s, expr* i, expr* l) {
        expr_ref len(a.mk_add(l, i), m);
        m_rewrite(len);
        return seq.str.is_length(len, l) && l == s;
    }


    /*
      s = ey
      l <= 0 => e = empty
      0 <= l <= len(s) => len(e) = l
      len(s) < l => e = s
    */
    void axioms::extract_prefix_axiom(expr* e, expr* s, expr* l) {
        
        TRACE("seq", tout << "prefix " << mk_bounded_pp(e, m, 2) << " " << mk_bounded_pp(s, m, 2) << " " << mk_bounded_pp(l, m, 2) << "\n";);
        expr_ref le = mk_len(e);
        expr_ref ls = mk_len(s);
        expr_ref ls_minus_l(mk_sub(ls, l), m);
        expr_ref y = m_sk.mk_post(s, l);
        expr_ref ey = mk_concat(e, y);
        expr_ref l_le_s = mk_le(mk_sub(l, ls), 0);
        add_clause(mk_seq_eq(s, ey));
        add_clause(~mk_le(l, 0), mk_eq_empty(e));
        add_clause(~mk_ge(l, 0), ~l_le_s, mk_eq(le, l));
        add_clause(l_le_s, mk_eq(e, s));
    }

    /*
      s = xe
      0 <= i <= len(s) => i = len(x)    
      i < 0 => e = empty
      i > len(s) => e = empty
    */
    void axioms::extract_suffix_axiom(expr* e, expr* s, expr* i) {
        TRACE("seq", tout << "suffix " << mk_bounded_pp(e, m, 2) << " " << mk_bounded_pp(s, m, 2) << "\n";);
        expr_ref x = m_sk.mk_pre(s, i);
        expr_ref lx = mk_len(x);
        expr_ref ls = mk_len(s);
        expr_ref xe = mk_concat(x, e);
        expr_ref emp = mk_eq_empty(e);
        expr_ref i_ge_0 = mk_ge(i, 0);
        expr_ref i_le_s = mk_le(mk_sub(i, ls), 0);
        add_clause(mk_eq(s, xe));
        add_clause(~i_ge_0, ~i_le_s, mk_eq(i, lx));
        add_clause(i_ge_0, emp);
        add_clause(i_le_s, emp);
    }        
    

    /*
      encode that s is not contained in of xs1
      where s1 is all of s, except the last element.
  
      s = "" or s = s1*(unit c)
      s = "" or !contains(x*s1, s)
    */
    void axioms::tightest_prefix(expr* s, expr* x) {
        expr_ref s_eq_emp = mk_eq_empty(s);
        if (seq.str.max_length(s) <= 1) {
            add_clause(s_eq_emp, ~expr_ref(seq.str.mk_contains(x, s), m));
            return;
        }
        expr_ref s1 = m_sk.mk_first(s);
        expr_ref c  = m_sk.mk_last(s);
        expr_ref s1c = mk_concat(s1, seq.str.mk_unit(c));
        add_clause(s_eq_emp, mk_seq_eq(s, s1c));
        add_clause(s_eq_emp, ~expr_ref(seq.str.mk_contains(mk_concat(x, s1), s), m));
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
    void axioms::indexof_axiom(expr* i) {
        expr* _s = nullptr, *_t = nullptr, *_offset = nullptr;
        rational r;
        VERIFY(seq.str.is_index(i, _t, _s) ||
               seq.str.is_index(i, _t, _s, _offset));
        expr_ref minus_one(a.mk_int(-1), m);
        expr_ref zero(a.mk_int(0), m);
        auto offset = purify(_offset);
        auto s = purify(_s);
        auto t = purify(_t);
        expr_ref xsy(m);
        expr_ref cnt(seq.str.mk_contains(t, s), m);
        expr_ref i_eq_m1 = mk_eq(i, minus_one);
        expr_ref i_eq_0 = mk_eq(i, zero);
        expr_ref s_eq_empty = mk_eq(s, seq.str.mk_empty(s->get_sort()));
        expr_ref t_eq_empty = mk_eq_empty(t);

        // |t| = 0 => |s| = 0 or indexof(t,s,offset) = -1
        // ~contains(t,s) => indexof(t,s,offset) = -1

        add_clause(cnt,  i_eq_m1);
        add_clause(~t_eq_empty, s_eq_empty, i_eq_m1);

        if (!offset || (a.is_numeral(offset, r) && r.is_zero())) {
            // |s| = 0 => indexof(t,s,0) = 0
            add_clause(~s_eq_empty, i_eq_0);
#if 1
            expr_ref x  = m_sk.mk_indexof_left(t, s);
            expr_ref y  = m_sk.mk_indexof_right(t, s);
            xsy         = mk_concat(x, s, y);
            expr_ref lenx = mk_len(x);
            // contains(t,s) & |s| != 0 => t = xsy & indexof(t,s,0) = |x|
            add_clause(~cnt, s_eq_empty, mk_seq_eq(t, xsy));
            add_clause(~cnt, s_eq_empty, mk_eq(i, lenx));
            add_clause(~cnt, mk_ge(i, 0));
            tightest_prefix(s, x);
#else
            // let i := indexof(t,s,0)
            // contains(t, s) & |s| != 0 => ~contains(substr(t,0,i+len(s)-1), s)
            //                           => substr(t,0,i+len(s)) = substr(t,0,i) ++ s
            //
            expr_ref len_s = mk_len(s);
            expr_ref mone(a.mk_int(-1), m);
            add_clause(~cnt, s_eq_empty, ~mk_literal(seq.str.mk_contains(seq.str.mk_substr(t,zero,a.mk_add(i,len_s,mone)),s)));
            add_clause(~cnt, s_eq_empty, mk_seq_eq(seq.str.mk_substr(t,zero,a.mk_add(i,len_s)),
                                                  seq.str.mk_concat(seq.str.mk_substr(t,zero,i), s)));
#endif
        }
        else {
            // offset >= len(t) => |s| = 0 or indexof(t, s, offset) = -1
            // offset > len(t) => indexof(t, s, offset) = -1
            // offset = len(t) & |s| = 0 => indexof(t, s, offset) = offset
            expr_ref len_t = mk_len(t);
            expr_ref offset_ge_len = mk_ge(mk_sub(offset, len_t), 0);
            expr_ref offset_le_len = mk_le(mk_sub(offset, len_t), 0);
            expr_ref i_eq_offset = mk_eq(i, offset);
            add_clause(~offset_ge_len, s_eq_empty, i_eq_m1);
            add_clause(offset_le_len, i_eq_m1);
            add_clause(~offset_ge_len, ~offset_le_len, ~s_eq_empty, i_eq_offset);

            expr_ref x = m_sk.mk_indexof_left(t, s, offset);
            expr_ref y = m_sk.mk_indexof_right(t, s, offset);
            expr_ref indexof0(seq.str.mk_index(y, s, zero), m);
            expr_ref offset_p_indexof0(a.mk_add(offset, indexof0), m);
            expr_ref offset_ge_0 = mk_ge(offset, 0);

            // 0 <= offset & offset < len(t) => t = xy
            // 0 <= offset & offset < len(t) => len(x) = offset
            // 0 <= offset & offset < len(t) & indexof(y,s,0) = -1 => -1 = i
            // 0 <= offset & offset < len(t) & indexof(y,s,0) >= 0 =>
            //                  indexof(y,s,0) + offset = indexof(t, s, offset)

            add_clause(~offset_ge_0, offset_ge_len, mk_seq_eq(t, mk_concat(x, y)));
            add_clause(~offset_ge_0, offset_ge_len, mk_eq(mk_len(x), offset));
            add_clause(~offset_ge_0, offset_ge_len,
                      ~mk_eq(indexof0, minus_one), i_eq_m1);
            add_clause(~offset_ge_0, offset_ge_len,
                      ~mk_ge(indexof0, 0),
                      mk_eq(offset_p_indexof0, i));

            // offset < 0 => -1 = i        
            add_clause(offset_ge_0, i_eq_m1);
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
    void axioms::last_indexof_axiom(expr* i) {
        expr* _s = nullptr, *_t = nullptr;
        VERIFY(seq.str.is_last_index(i, _t, _s));
        auto t = purify(_t);
        auto s = purify(_s);
        expr_ref minus_one(a.mk_int(-1), m);
        expr_ref zero(a.mk_int(0), m);
        expr_ref x  = m_sk.mk_last_indexof_left(t, s);
        expr_ref y  = m_sk.mk_last_indexof_right(t, s);
        expr_ref s_head(m), s_tail(m);
        m_sk.decompose(s, s_head, s_tail);
        expr_ref cnt        = expr_ref(seq.str.mk_contains(t, s), m);
        expr_ref cnt2       = expr_ref(seq.str.mk_contains(mk_concat(s_tail, y), s), m);
        expr_ref i_eq_m1    = mk_eq(i, minus_one);
        expr_ref i_eq_0     = mk_eq(i, zero);
        expr_ref s_eq_empty = mk_eq_empty(s);
        expr_ref t_eq_empty = mk_eq_empty(t);
        expr_ref xsy        = mk_concat(x, s, y);

        add_clause(cnt, i_eq_m1);
        add_clause(~t_eq_empty, s_eq_empty, i_eq_m1);
        add_clause(~t_eq_empty, ~s_eq_empty, i_eq_0);
        add_clause(t_eq_empty, ~cnt, mk_seq_eq(t, xsy));
        add_clause(t_eq_empty, ~cnt, mk_eq(i, mk_len(x)));
        add_clause(s_eq_empty, mk_eq(s, mk_concat(s_head, s_tail)));
        add_clause(s_eq_empty, ~cnt2);
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
    void axioms::replace_axiom(expr* r) {
        expr* _u = nullptr, *_s = nullptr, *_t = nullptr;
        VERIFY(seq.str.is_replace(r, _u, _s, _t));
        auto u = purify(_u);
        auto s = purify(_s);
        auto t = purify(_t);
        expr_ref x  = m_sk.mk_indexof_left(u, s);
        expr_ref y  = m_sk.mk_indexof_right(u, s);
        expr_ref xty = mk_concat(x, t, y);
        expr_ref xsy = mk_concat(x, s, y);
        expr_ref u_emp = mk_eq_empty(u);
        expr_ref s_emp = mk_eq_empty(s);
        expr_ref cnt = expr_ref(seq.str.mk_contains(u, s), m);
        add_clause(~s_emp, mk_seq_eq(r, mk_concat(t, u)));
        add_clause(~u_emp, s_emp, mk_seq_eq(r, u));
        add_clause(cnt,  mk_seq_eq(r, u));
        add_clause(~cnt, u_emp, s_emp, mk_seq_eq(u, xsy));
        add_clause(~cnt, u_emp, s_emp, mk_seq_eq(r, xty));
        tightest_prefix(s, x);
    }

    /*
      let e = at(s, i)

      0 <= i < len(s) -> s = xey & len(x) = i & len(e) = 1
      i < 0 \/ i >= len(s) -> e = empty

    */
    void axioms::at_axiom(expr* e) {
        TRACE("seq", tout << "at-axiom: " << mk_bounded_pp(e, m) << "\n";);
        expr* _s = nullptr, *_i = nullptr;
        VERIFY(seq.str.is_at(e, _s, _i));
        auto s = purify(_s);
        auto i = purify(_i);
        expr_ref zero(a.mk_int(0), m);
        expr_ref one(a.mk_int(1), m);
        expr_ref emp(seq.str.mk_empty(e->get_sort()), m);
        expr_ref len_s = mk_len(s);
        expr_ref i_ge_0 = mk_ge(i, 0);
        expr_ref i_ge_len_s = mk_ge(mk_sub(i, mk_len(s)), 0);
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
            add_clause(~i_ge_0, i_ge_len_s, mk_seq_eq(s, seq.str.mk_concat(es, e->get_sort())));
            add_clause(~i_ge_0, i_ge_len_s, mk_seq_eq(nth, e));                
        }
        else {
            expr_ref x =     m_sk.mk_pre(s, i);
            expr_ref y =     m_sk.mk_tail(s, i);
            expr_ref xey   = mk_concat(x, e, y);
            expr_ref len_x = mk_len(x);
            add_clause(~i_ge_0, i_ge_len_s, mk_seq_eq(s, xey));
            add_clause(~i_ge_0, i_ge_len_s, mk_eq(i, len_x));
        }

        add_clause(i_ge_0, mk_eq(e, emp));
        add_clause(~i_ge_len_s, mk_eq(e, emp));
        add_clause(~i_ge_0, i_ge_len_s, mk_eq(one, len_e));
        add_clause(mk_le(len_e, 1));
    }


    /**
       i >= 0 i < len(s) => unit(nth_i(s, i)) = at(s, i)
       nth_i(unit(nth_i(s, i)), 0) = nth_i(s, i)
    */

    void axioms::nth_axiom(expr* e) {
        expr* s = nullptr, *i = nullptr;
        rational n;
        zstring str;
        VERIFY(seq.str.is_nth_i(e, s, i));
        if (seq.str.is_string(s, str) && a.is_numeral(i, n) && 
            n.is_unsigned() && n.get_unsigned() < str.length()) {
            app_ref ch(seq.str.mk_char(str[n.get_unsigned()]), m);
            add_clause(mk_eq(ch, e));
        }
        else {
            expr_ref zero(a.mk_int(0), m);
            expr_ref i_ge_0 =     mk_ge(i, 0);
            expr_ref i_ge_len_s = mk_ge(mk_sub(i, mk_len(s)), 0);
            // at(s,i) = [nth(s,i)]
            expr_ref rhs(s, m);
            expr_ref lhs(seq.str.mk_unit(e), m);
            if (!seq.str.is_at(s) || zero != i) rhs = seq.str.mk_at(s, i);
            m_rewrite(rhs);
            add_clause(~i_ge_0, i_ge_len_s, mk_eq(lhs, rhs));
        }
    }


    void axioms::itos_axiom(expr* e) {
        expr* n = nullptr;
        TRACE("seq", tout << mk_pp(e, m) << "\n";);
        VERIFY(seq.str.is_itos(e, n));

        // itos(n) = "" <=> n < 0
        expr_ref zero(a.mk_int(0), m);
        expr_ref eq1 = expr_ref(seq.str.mk_is_empty(e), m);
        expr_ref ge0 = mk_ge(n, 0);
        // n >= 0 => itos(n) != ""
        // itos(n) = "" or n >= 0
        add_clause(~eq1, ~ge0);
        add_clause(eq1, ge0);
        add_clause(mk_ge(mk_len(e), 0));
    
        // n >= 0 => stoi(itos(n)) = n
        app_ref stoi(seq.str.mk_stoi(e), m);
        expr_ref eq = mk_eq(stoi, n);
        add_clause(~ge0, eq);
        m_set_phase(eq);

        // itos(n) does not start with "0" when n > 0
        // n = 0 or at(itos(n),0) != "0"
        // alternative: n >= 0 => itos(stoi(itos(n))) = itos(n)
        expr_ref zs(seq.str.mk_string("0"), m);
        m_rewrite(zs);
        expr_ref eq0 = mk_eq(n, zero);
        expr_ref at0 = mk_eq(seq.str.mk_at(e, zero), zs);
        add_clause(eq0, ~at0);
        add_clause(~eq0, mk_eq(e, zs));
    }

    /**
       stoi(s) >= -1
       stoi("") = -1
       stoi(s) >= 0 => is_digit(nth(s,0)) 
       stoi(s) >= 0 => len(s) >= 1
    */
    void axioms::stoi_axiom(expr* e) {
        TRACE("seq", tout << mk_pp(e, m) << "\n";);
        expr_ref ge0 = mk_ge(e, 0);      
        expr* s = nullptr;
        VERIFY (seq.str.is_stoi(e, s));    
        add_clause(mk_ge(e, -1));                             // stoi(s) >= -1
        add_clause(mk_eq(seq.str.mk_stoi(seq.str.mk_empty(s->get_sort())), a.mk_int(-1)));
//      add_clause(~mk_eq_empty(s), mk_eq(e, a.mk_int(-1)));  // s = "" => stoi(s) = -1
        add_clause(~ge0, is_digit(mk_nth(s, 0)));             // stoi(s) >= 0 => is_digit(nth(s,0))
        add_clause(~ge0, mk_ge(mk_len(s), 1));                // stoi(s) >= 0 => len(s) >= 1
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
    void axioms::stoi_axiom(expr* e, unsigned k) {
        SASSERT(k > 0);
        expr* _s = nullptr;
        VERIFY (seq.str.is_stoi(e, _s));
        expr_ref s(_s, m);
        m_rewrite(s);
        auto stoi2 = [&](unsigned j) { return m_sk.mk("seq.stoi", s, a.mk_int(j), a.mk_int()); }; 
        auto digit = [&](unsigned j) { return mk_digit2int(mk_nth(s, j)); };
        auto is_digit_ = [&](unsigned j) { return is_digit(mk_nth(s, j)); };
        expr_ref len = mk_len(s);
        expr_ref ge0 = mk_ge(e, 0);
        expr_ref lek = mk_le(len, k);
        add_clause(~lek, mk_eq(e, stoi2(k-1)));                                    // len(s) <= k  => stoi(s) = stoi(s, k-1)
        add_clause(mk_le(len, 0), ~is_digit_(0), mk_eq(stoi2(0), digit(0)));       // len(s) > 0, is_digit(nth(s, 0)) => stoi(s,0) = digit(s,0)
        add_clause(mk_le(len, 0), is_digit_(0),  mk_eq(stoi2(0), a.mk_int(-1)));   // len(s) > 0, ~is_digit(nth(s, 0)) => stoi(s,0) = -1
        for (unsigned i = 1; i < k; ++i) {

            // len(s) <= i => stoi(s, i) = stoi(s, i - 1)

            add_clause(~mk_le(len, i),  mk_eq(stoi2(i), stoi2(i-1)));

            // len(s) > i, stoi(s, i - 1) >= 0, is_digit(nth(s, i)) => stoi(s, i) = 10*stoi(s, i - 1) + digit(i)
            // len(s) > i, stoi(s, i - 1) < 0 => stoi(s, i) = -1
            // len(s) > i, ~is_digit(nth(s, i)) => stoi(s, i) = -1

            add_clause(mk_le(len, i), ~mk_ge(stoi2(i-1), 0), ~is_digit_(i), mk_eq(stoi2(i), a.mk_add(a.mk_mul(a.mk_int(10), stoi2(i-1)), digit(i))));
            add_clause(mk_le(len, i), is_digit_(i),                         mk_eq(stoi2(i), a.mk_int(-1)));
            add_clause(mk_le(len, i), mk_ge(stoi2(i-1), 0),                 mk_eq(stoi2(i), a.mk_int(-1)));

            // stoi(s) >= 0, i < len(s) => is_digit(nth(s, i))

            add_clause(~ge0, mk_le(len, i), is_digit_(i));
        }
    }

    void axioms::ubv2s_axiom(expr* b, unsigned k) {
        expr_ref ge10k(m), ge10k1(m), eq(m);
        bv_util bv(m);
        sort* bv_sort = b->get_sort();
        rational pow(1);
        for (unsigned i = 0; i < k; ++i)
            pow *= 10;
        if (k == 0) {
            ge10k = m.mk_true();            
        }
        else {
            ge10k = bv.mk_ule(bv.mk_numeral(pow, bv_sort), b);
        }
        ge10k1 = bv.mk_ule(bv.mk_numeral(pow * 10, bv_sort), b);
        unsigned sz = bv.get_bv_size(b);
        expr_ref_vector es(m);
        expr_ref bb(b, m), ten(bv.mk_numeral(10, sz), m);
        pow = 1;
        for (unsigned i = 0; i <= k; ++i) {
            if (pow > 1)
                bb = bv.mk_bv_udiv(b, bv.mk_numeral(pow, bv_sort));
            es.push_back(seq.str.mk_unit(m_sk.mk_ubv2ch(bv.mk_bv_urem(bb, ten))));
            pow *= 10;
        }
        es.reverse();
        eq = m.mk_eq(seq.str.mk_ubv2s(b), seq.str.mk_concat(es, seq.str.mk_string_sort()));
        add_clause(~ge10k, ge10k1, eq);
    }

    /*
    *   len(ubv2s(b)) = k => 10^k-1 <= b < 10^{k}   k > 1
    *   len(ubv2s(b)) = 1 =>  b < 10^{1}   k = 1
    */
    void axioms::ubv2s_len_axiom(expr* b, unsigned k) {
        expr_ref ge10k(m), ge10k1(m), eq(m);
        bv_util bv(m);
        sort* bv_sort = b->get_sort();
        unsigned sz = bv.get_bv_size(bv_sort);
        rational pow(1);
        for (unsigned i = 1; i < k; ++i)
            pow *= 10;
        if (pow * 10 >= rational::power_of_two(sz))
            return; // TODO: add conflict when k is too large or avoid overflow bounds and limits
        ge10k = bv.mk_ule(bv.mk_numeral(pow, bv_sort), b);        
        ge10k1 = bv.mk_ule(bv.mk_numeral(pow * 10, bv_sort), b);
        eq = m.mk_eq(seq.str.mk_length(seq.str.mk_ubv2s(b)), a.mk_int(k));
        add_clause(~eq, ~ge10k1);
        if (k > 1)
            add_clause(~eq, ge10k);
    }

    void axioms::ubv2ch_axiom(sort* bv_sort) {
        bv_util bv(m);
        expr_ref eq(m);
        unsigned sz = bv.get_bv_size(bv_sort);
        for (unsigned i = 0; i < 10; ++i) {
            eq = m.mk_eq(m_sk.mk_ubv2ch(bv.mk_numeral(i, sz)), seq.mk_char('0' + i));
            add_clause(eq);
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

    void axioms::itos_axiom(expr* s, unsigned k) {
        expr* e = nullptr;
        VERIFY(seq.str.is_itos(s, e));
        expr_ref len = mk_len(s);
        add_clause(mk_ge(e, 10), mk_le(len, 1));
        add_clause(mk_le(e, -1), mk_ge(len, 1));
        rational lo(1);
        for (unsigned i = 1; i <= k; ++i) {
            lo *= rational(10);
            add_clause(mk_ge(e, lo), mk_le(len, i));
            add_clause(mk_le(e, lo - 1), mk_ge(len, i + 1));
        }
    }

    expr_ref axioms::is_digit(expr* ch) {
        return expr_ref(seq.mk_char_is_digit(ch), m);
    }

    expr_ref axioms::mk_digit2int(expr* ch) {
        m_ensure_digits();
        return expr_ref(m_sk.mk_digit2int(ch), m);
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
    void axioms::lt_axiom(expr* n) {
        expr* _e1 = nullptr, *_e2 = nullptr;
        VERIFY(seq.str.is_lt(n, _e1, _e2));
        auto e1 = purify(_e1);
        auto e2 = purify(_e2);
        sort* s = e1->get_sort();
        sort* char_sort = nullptr;
        VERIFY(seq.is_seq(s, char_sort));
        expr_ref lt = expr_ref(n, m);
        expr_ref x = m_sk.mk("str.<.x", e1, e2);
        expr_ref y = m_sk.mk("str.<.y", e1, e2);
        expr_ref z = m_sk.mk("str.<.z", e1, e2);
        expr_ref c = m_sk.mk("str.<.c", e1, e2, char_sort);
        expr_ref d = m_sk.mk("str.<.d", e1, e2, char_sort);
        expr_ref xcy = mk_concat(x, seq.str.mk_unit(c), y);
        expr_ref xdz = mk_concat(x, seq.str.mk_unit(d), z);
        expr_ref eq   = mk_eq(e1, e2);
        expr_ref pref21 = expr_ref(seq.str.mk_prefix(e2, e1), m);
        expr_ref pref12 = expr_ref(seq.str.mk_prefix(e1, e2), m);
        expr_ref e1xcy = mk_eq(e1, xcy);
        expr_ref e2xdz = mk_eq(e2, xdz);
        expr_ref ltcd = expr_ref(seq.mk_lt(c, d), m);
        expr_ref ltdc = expr_ref(seq.mk_lt(d, c), m);
        add_clause(~lt, pref12, e2xdz);
        add_clause(~lt, pref12, e1xcy);
        add_clause(~lt, pref12, ltcd);
        add_clause(lt, pref21, e1xcy);
        add_clause(lt, pref21, ltdc);
        add_clause(lt, pref21, e2xdz);
        add_clause(~eq, ~lt);
    }

    /**
       e1 <= e2 <=> e1 < e2 or e1 = e2
    */
    void axioms::le_axiom(expr* n) {
        expr* e1 = nullptr, *e2 = nullptr;
        VERIFY(seq.str.is_le(n, e1, e2));
        expr_ref lt = expr_ref(seq.str.mk_lex_lt(e1, e2), m);
        expr_ref le = expr_ref(n, m);
        expr_ref eq = mk_eq(e1, e2);
        add_clause(~le, lt, eq);
        add_clause(~eq, le);
        add_clause(~lt, le);
    }

    /**
       is_digit(e) <=> to_code('0') <= to_code(e) <= to_code('9')
    */
    void axioms::is_digit_axiom(expr* n) {
        expr* e = nullptr;
        VERIFY(seq.str.is_is_digit(n, e)); 
        expr_ref is_digit = expr_ref(n, m);
        expr_ref to_code(seq.str.mk_to_code(e), m);
        expr_ref ge0 = mk_ge(to_code, (unsigned)'0');
        expr_ref le9 = mk_le(to_code, (unsigned)'9');
        add_clause(~is_digit, ge0);
        add_clause(~is_digit, le9);
        add_clause(is_digit, ~ge0, ~le9);
    }

    /**
       len(e) = 1 => 0 <= to_code(e) <= max_code
       len(e) = 1 => from_code(to_code(e)) = e
       len(e) != 1 => to_code(e) = -1
    */
    void axioms::str_to_code_axiom(expr* n) {
        expr* e = nullptr;
        VERIFY(seq.str.is_to_code(n, e)); 
        expr_ref len_is1 = mk_eq(mk_len(e), a.mk_int(1));
        add_clause(~len_is1, mk_ge(n, 0)); 
        add_clause(~len_is1, mk_le(n, seq.max_char()));
        add_clause(~len_is1, mk_eq(n, seq.mk_char2int(mk_nth(e, 0))));
        if (!seq.str.is_from_code(e))
            add_clause(~len_is1, mk_eq(e, seq.str.mk_from_code(n)));
        add_clause(len_is1, mk_eq(n, a.mk_int(-1)));
    }

    /**
       0 <= e <= max_char => len(from_code(e)) = 1
       0 <= e <= max_char => to_code(from_code(e)) = e
       e < 0 or e > max_char => len(from_code(e)) = ""
    */
    void axioms::str_from_code_axiom(expr* n) {
        expr* e = nullptr;
        VERIFY(seq.str.is_from_code(n, e)); 
        expr_ref ge = mk_ge(e, 0);
        expr_ref le = mk_le(e, seq.max_char());
        expr_ref emp = expr_ref(seq.str.mk_is_empty(n), m);
        add_clause(~ge, ~le, mk_eq(mk_len(n), a.mk_int(1)));
        if (!seq.str.is_to_code(e))
            add_clause(~ge, ~le, mk_eq(seq.str.mk_to_code(n), e));
        add_clause(ge, emp);
        add_clause(le, emp);
    }


    /**
       Unit is injective:

       u = inv-unit(unit(u)) 
    */

    void axioms::unit_axiom(expr* n) {
        expr* u = nullptr;
        VERIFY(seq.str.is_unit(n, u));
        add_clause(mk_eq(u, m_sk.mk_unit_inv(n)));
    }

    /**

       suffix(s, t) => s = seq.suffix_inv(s, t) + t
       ~suffix(s, t) => len(s) > len(t) or s = y(s, t) + unit(c(s, t)) + x(s, t)
       ~suffix(s, t) => len(s) > len(t) or t = z(s, t) + unit(d(s, t)) + x(s, t)
       ~suffix(s, t) => len(s) > len(t) or c(s,t) != d(s,t)

    */

    void axioms::suffix_axiom(expr* e) {
        expr* _s = nullptr, *_t = nullptr;
        VERIFY(seq.str.is_suffix(e, _s, _t));
        auto s = purify(_s);
        auto t = purify(_t);
        expr_ref lit = expr_ref(e, m);
        expr_ref s_gt_t = mk_ge(mk_sub(mk_len(s), mk_len(t)), 1);
#if 0
        expr_ref x = m_sk.mk_pre(t, mk_sub(mk_len(t), mk_len(s)));
        expr_ref y = m_sk.mk_tail(t, mk_sub(mk_len(s), a.mk_int(1)));
        add_clause(lit, s_gt_t, mk_seq_eq(t, mk_concat(x, y)));
        add_clause(lit, s_gt_t, mk_eq(mk_len(y), mk_len(s)));
        add_clause(lit, s_gt_t, ~mk_eq(y, s));    
#else
        sort* char_sort = nullptr;
        VERIFY(seq.is_seq(s->get_sort(), char_sort));
        expr_ref x = m_sk.mk("seq.suffix.x", s, t);
        expr_ref y = m_sk.mk("seq.suffix.y", s, t);
        expr_ref z = m_sk.mk("seq.suffix.z", s, t);
        expr_ref c = m_sk.mk("seq.suffix.c", s, t, char_sort);
        expr_ref d = m_sk.mk("seq.suffix.d", s, t, char_sort);
        add_clause(lit, s_gt_t, mk_seq_eq(s, mk_concat(y, seq.str.mk_unit(c), x)));
        add_clause(lit, s_gt_t, mk_seq_eq(t, mk_concat(z, seq.str.mk_unit(d), x)));
        add_clause(lit, s_gt_t, ~mk_eq(c, d));
#endif
    }

    void axioms::prefix_axiom(expr* e) {
        expr* _s = nullptr, *_t = nullptr;
        VERIFY(seq.str.is_prefix(e, _s, _t));
        auto s = purify(_s);
        auto t = purify(_t);
        expr_ref lit = expr_ref(e, m);
        expr_ref s_gt_t = mk_ge(mk_sub(mk_len(s), mk_len(t)), 1);
#if 0
        expr_ref x = m_sk.mk_pre(t, mk_len(s));    
        expr_ref y = m_sk.mk_tail(t, mk_sub(mk_sub(mk_len(t), mk_len(s)), a.mk_int(1)));
        add_clause(lit, s_gt_t, mk_seq_eq(t, mk_concat(x, y)));
        add_clause(lit, s_gt_t, mk_eq(mk_len(x), mk_len(s)));
        add_clause(lit, s_gt_t, ~mk_eq(x, s));

#else
        sort* char_sort = nullptr;
        VERIFY(seq.is_seq(s->get_sort(), char_sort));
        expr_ref x = m_sk.mk("seq.prefix.x", s, t);
        expr_ref y = m_sk.mk("seq.prefix.y", s, t);
        expr_ref z = m_sk.mk("seq.prefix.z", s, t);
        expr_ref c = m_sk.mk("seq.prefix.c", s, t, char_sort);
        expr_ref d = m_sk.mk("seq.prefix.d", s, t, char_sort);
        add_clause(lit, s_gt_t, mk_seq_eq(s, mk_concat(x, seq.str.mk_unit(c), y)));
        add_clause(lit, s_gt_t, mk_seq_eq(t, mk_concat(x, seq.str.mk_unit(d), z)), mk_seq_eq(t, x));
        add_clause(lit, s_gt_t, ~mk_eq(c, d));
#endif
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
    void axioms::length_axiom(expr* n) {
        expr* x = nullptr;
        VERIFY(seq.str.is_length(n, x));
        if (seq.str.is_concat(x) ||
            seq.str.is_unit(x) ||
            seq.str.is_empty(x) ||
            seq.str.is_string(x)) {
            expr_ref len(n, m);
            m_rewrite(len);
            SASSERT(n != len);
            add_clause(mk_eq(len, n));
        }
        else {
            add_clause(mk_ge(n, 0));
        }
    }


    /**
       ~contains(a, b) => ~prefix(b, a)
       ~contains(a, b) => ~contains(tail(a), b) or a = empty
       ~contains(a, b) & a = empty => b != empty
       ~(a = empty) => a = head + tail 
    */
    void axioms::unroll_not_contains(expr* e) {
        expr_ref head(m), tail(m);
        expr* a = nullptr, *b = nullptr;
        VERIFY(seq.str.is_contains(e, a, b));
        m_sk.decompose(a, head, tail);
        expr_ref pref(seq.str.mk_prefix(b, a), m);
        expr_ref postf(seq.str.mk_contains(tail, b), m);
        expr_ref emp = mk_eq_empty(a);
        expr_ref cnt = expr_ref(e, m);
        add_clause(cnt, ~pref);
        add_clause(cnt, ~postf);
        add_clause(~emp, mk_eq_empty(tail));
        add_clause(emp, mk_eq(a, seq.str.mk_concat(head, tail)));
    }

    expr_ref axioms::length_limit(expr* s, unsigned k) {
        expr_ref bound_tracker = m_sk.mk_length_limit(s, k);
        expr* s0 = nullptr;
        if (seq.str.is_stoi(s, s0)) 
            s = s0; 
        add_clause(~bound_tracker, mk_le(mk_len(s), k));
        return bound_tracker;
    }

}
