/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    seq_skolem.h

Abstract:

    Skolem function support for sequences.
    Skolem functions are auxiliary funcions useful for axiomatizing sequence
    operations.

Author:

    Nikolaj Bjorner (nbjorner) 2020-4-16

--*/
#pragma once

#include "ast/seq_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/rewriter/th_rewriter.h"

namespace seq {

    class skolem {
        ast_manager&   m;
        th_rewriter&   m_rewrite; // NB: would be nicer not to have this dependency
        seq_util       seq;
        arith_util     a;

        symbol         m_prefix, m_suffix;
        symbol         m_tail;
        symbol         m_seq_first, m_seq_last; 
        symbol         m_indexof_left, m_indexof_right;   // inverse of indexof: (indexof_left s t) + s + (indexof_right s t) = t, for s in t. 
        symbol         m_aut_step;                        // regex unfolding state
        symbol         m_accept;                          // regex
        symbol         m_is_empty, m_is_non_empty;        // regex emptiness check
        symbol         m_pre, m_post;                     // inverse of at: (pre s i) + (at s i) + (post s i) = s if 0 <= i < (len s)
        symbol         m_eq;                              // equality atom
        symbol         m_max_unfolding, m_length_limit;

    public:

        skolem(ast_manager& m, th_rewriter& r);

        expr_ref mk(symbol const& s, sort* range) { return mk(s, nullptr, nullptr, nullptr, nullptr, range); }
        expr_ref mk(symbol const& s, expr* e, sort* range) { return mk(s, e, nullptr, nullptr, nullptr, range); }
        expr_ref mk(symbol const& s, expr* e1, expr* e2, sort* range) { return mk(s, e1, e2, nullptr, nullptr, range); }
        expr_ref mk(symbol const& s, expr* e1, expr* e2, expr* e3, sort* range, bool rw = true) { return mk(s, e1, e2, e3, nullptr, range, rw); }
        expr_ref mk(symbol const& s, expr* e1, expr* e2 = nullptr, expr* e3 = nullptr, expr* e4 = nullptr, sort* range = nullptr, bool rw = true);

        expr_ref mk(char const* s, sort* range) { return mk(s, nullptr, nullptr, nullptr, nullptr, range); }
        expr_ref mk(char const* s, expr* e, sort* range) { return mk(s, e, nullptr, nullptr, nullptr, range); }
        expr_ref mk(char const* s, expr* e1, expr* e2, sort* range) { return mk(s, e1, e2, nullptr, nullptr, range); }
        expr_ref mk(char const* s, expr* e1, expr* e2, expr* e3, sort* range) { return mk(s, e1, e2, e3, nullptr, range); }
        expr_ref mk(char const* s , expr* e1, expr* e2 = nullptr, expr* e3 = nullptr, expr* e4 = nullptr, sort* range = nullptr) {
            return mk(symbol(s), e1, e2, e3, e4, range);
        }

        expr_ref mk_align(expr* e1, expr* e2, expr* e3, expr* e4) { return mk("seq.align", e1, e2, e3, e4); }
        expr_ref mk_align_l(expr* e1, expr* e2, expr* e3, expr* e4) { return mk("seq.align.l", e1, e2, e3, e4); }
        expr_ref mk_align_r(expr* e1, expr* e2, expr* e3, expr* e4) { return mk("seq.align.r", e1, e2, e3, e4); }
        expr_ref mk_align_m(expr* e1, expr* e2, expr* e3, expr* e4) {
            expr* x1 = nullptr, *x2 = nullptr, *y1 = nullptr, *y2 = nullptr;
            if (is_align(e1, x1, x2) && is_align(e2, y1, y2)) {
                if (x2 == y2 && x1 != y1)
                    return mk_align_m(x1, y1, e3, e4);
            }
            return mk("seq.align.m", e1, e2, e3, e4);
        }
        expr_ref mk_accept(expr_ref_vector const& args) { return expr_ref(seq.mk_skolem(m_accept, args.size(), args.data(), m.mk_bool_sort()), m); }
        expr_ref mk_accept(expr* s, expr* i, expr* r) { return mk(m_accept, s, i, r, nullptr, m.mk_bool_sort()); }
        expr_ref mk_is_non_empty(expr* r, expr* u, expr* n) { return mk(m_is_non_empty, r, u, n, m.mk_bool_sort(), false); }
        expr_ref mk_is_empty(expr* r, expr* u, expr* n) { return mk(m_is_empty, r, u, n, m.mk_bool_sort(), false); }

        expr_ref mk_indexof_left(expr* t, expr* s, expr* offset = nullptr) { return mk(m_indexof_left, t, s, offset); }
        expr_ref mk_indexof_right(expr* t, expr* s, expr* offset = nullptr) { return mk(m_indexof_right, t, s, offset); }
        expr_ref mk_last_indexof_left(expr* t, expr* s, expr* offset = nullptr) { return mk("seq.last_indexof_left", t, s, offset); }
        expr_ref mk_last_indexof_right(expr* t, expr* s, expr* offset = nullptr) { return mk("seq.last_indexof_right", t, s, offset); }

        expr_ref mk_tail(expr* s, expr* i) { return mk(m_tail, s, i); }
        expr_ref mk_post(expr* s, expr* i) { return mk(m_post, s, i); }
        expr_ref mk_ite(expr* c, expr* t, expr* e) { return mk(symbol("seq.if"), c, t, e, nullptr, t->get_sort()); }
        expr_ref mk_last(expr* s);
        expr_ref mk_first(expr* s);
        expr_ref mk_pre(expr* s, expr* i) { return mk(m_pre, s, i); }
        expr_ref mk_eq(expr* a, expr* b) { return mk(m_eq, a, b, nullptr, nullptr, m.mk_bool_sort()); }
        expr_ref mk_prefix_inv(expr* s, expr* t) { return mk(m_prefix, s, t); }
        expr_ref mk_suffix_inv(expr* s, expr* t) { return mk(m_suffix, s, t); }
        expr_ref mk_step(expr* s, expr* idx, expr* re, unsigned i, unsigned j, expr* t);
        expr_ref mk_is_digit(expr* ch) { return mk(symbol("seq.is_digit"), ch, nullptr, nullptr, nullptr, m.mk_bool_sort()); }
        expr_ref mk_unit_inv(expr* n);
        expr_ref mk_digit2int(expr* ch) { return mk(symbol("seq.digit2int"), ch, nullptr, nullptr, nullptr, a.mk_int()); }
        expr_ref mk_digit2bv(expr* ch, sort* bv_sort);
        expr_ref mk_ubv2ch(expr* b) { return mk(symbol("seq.ubv2ch"), b, nullptr, nullptr, nullptr, seq.mk_char_sort()); }
        expr_ref mk_left(expr* x, expr* y, expr* z = nullptr) { return mk("seq.left", x, y, z); }
        expr_ref mk_right(expr* x, expr* y, expr* z = nullptr) { return mk("seq.right", x, y, z); }
        expr_ref mk_max_unfolding_depth(unsigned d);
        expr_ref mk_length_limit(expr* e, unsigned d);

        
        bool is_skolem(symbol const& s, expr const* e) const;
        bool is_skolem(expr const* e) const { return seq.is_skolem(e); }

        bool is_first(expr* e, expr*& u) { return is_skolem(m_seq_first, e) && (u = to_app(e)->get_arg(0), true); }
        bool is_last(expr* e, expr*& u) { return is_skolem(m_seq_last, e) && (u = to_app(e)->get_arg(0), true); }
        bool is_unit_inv(expr* e) const { return is_skolem(symbol("seq.unit-inv"), e); }
        bool is_unit_inv(expr* e, expr*& u) const { return is_unit_inv(e) && (u = to_app(e)->get_arg(0), true); }
        bool is_tail(expr* e) const { return is_skolem(m_tail, e); }
        bool is_seq_first(expr* e) const { return is_skolem(m_seq_first, e); }
        bool is_indexof_left(expr* e) const { return is_skolem(m_indexof_left, e); }
        bool is_indexof_right(expr* e) const { return is_skolem(m_indexof_right, e); }
        bool is_indexof_left(expr* e, expr*& x, expr*& y) const { 
            return is_indexof_left(e) && (x = to_app(e)->get_arg(0), y = to_app(e)->get_arg(1), true); 
        }
        bool is_indexof_right(expr* e, expr*& x, expr*& y) const { 
            return is_indexof_right(e) && (x = to_app(e)->get_arg(0), y = to_app(e)->get_arg(1), true); 
        }

        bool is_step(expr* e) const { return is_skolem(m_aut_step, e); }
        bool is_step(expr* e, expr*& s, expr*& idx, expr*& re, expr*& i, expr*& j, expr*& t) const;
        bool is_accept(expr* acc) const {  return is_skolem(m_accept, acc); }
        bool is_accept(expr* a, expr*& s, expr*& i, expr*& r, expr*& n) const { 
            return is_accept(a) && to_app(a)->get_num_args() == 4 && 
                (s = to_app(a)->get_arg(0), i = to_app(a)->get_arg(1), 
                 r = to_app(a)->get_arg(2), n = to_app(a)->get_arg(3), 
                 true); 
        }
        bool is_accept(expr* e, expr*& s, expr*& i, unsigned& idx, expr*& r) const {
            return is_accept(e) && to_app(e)->get_num_args() == 3 &&                
                (s = to_app(e)->get_arg(0), i = to_app(e)->get_arg(1),
                 r = to_app(e)->get_arg(2), true) && 
                a.is_unsigned(i, idx);
        }
        bool is_align(expr const* e) const { return is_skolem(symbol("seq.align.m"), e); }
        bool is_align_l(expr const* e) const { return is_skolem(symbol("seq.align.l"), e); }
        bool is_align_r(expr const* e) const { return is_skolem(symbol("seq.align.r"), e); }
        MATCH_BINARY(is_align);
        bool is_post(expr* e, expr*& s, expr*& start);
        bool is_pre(expr* e, expr*& s, expr*& i);
        bool is_eq(expr* e, expr*& a, expr*& b) const;
        bool is_tail(expr* e, expr*& s, expr*& idx) const;
        bool is_tail_u(expr* e, expr*& s, unsigned& idx) const;
        bool is_tail(expr* e, expr*& s) const;
        bool is_digit(expr* e) const { return is_skolem(symbol("seq.is_digit"), e); }
        bool is_max_unfolding(expr* e) const { return is_skolem(m_max_unfolding, e); }
        bool is_length_limit(expr* e) const { return is_skolem(m_length_limit, e); }
        bool is_length_limit(expr* p, unsigned& lim, expr*& s) const; 
        bool is_is_empty(expr* e) const { return is_skolem(m_is_empty, e); }
        bool is_is_non_empty(expr* e) const { return is_skolem(m_is_non_empty, e); }
        bool is_is_empty(expr* e, expr*& r, expr*& u, expr*& n) const { 
            return is_skolem(m_is_empty, e) && (r = to_app(e)->get_arg(0), u = to_app(e)->get_arg(1), n = to_app(e)->get_arg(2), true); 
        }
        bool is_is_non_empty(expr* e, expr*& r, expr*& u, expr*& n) const { 
            return is_skolem(m_is_non_empty, e) && (r = to_app(e)->get_arg(0), u = to_app(e)->get_arg(1), n = to_app(e)->get_arg(2), true); 
        }

        void decompose(expr* e, expr_ref& head, expr_ref& tail);

    };

};

