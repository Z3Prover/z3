/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    skolem.cpp

Author:

    Nikolaj Bjorner (nbjorner) 2020-4-16

--*/

#include "ast/rewriter/seq_skolem.h"
#include "ast/ast_pp.h"

using namespace seq;


skolem::skolem(ast_manager& m, th_rewriter& rw): 
    m(m), 
    m_rewrite(rw),
    seq(m),
    a(m) {
    m_prefix         = "seq.p.suffix";
    m_suffix         = "seq.s.prefix";
    m_accept         = "aut.accept";
    m_tail           = "seq.tail";
    m_seq_first      = "seq.first";
    m_seq_last       = "seq.last";
    m_indexof_left   = "seq.idx.left";
    m_indexof_right  = "seq.idx.right";
    m_aut_step       = "aut.step";
    m_pre            = "seq.pre";  // (seq.pre s l):  prefix of string s of length l
    m_post           = "seq.post"; // (seq.post s l): suffix of string s of length k, based on extract starting at index i of length l
    m_eq             = "seq.eq";
    m_max_unfolding  = "seq.max_unfolding";
    m_length_limit   = "seq.length_limit";
    m_is_empty       = "re.is_empty";
    m_is_non_empty   = "re.is_non_empty";
}

expr_ref skolem::mk(symbol const& s, expr* e1, expr* e2, expr* e3, expr* e4, sort* range, bool rw) {
    expr* es[4] = { e1, e2, e3, e4 };
    unsigned len = e4?4:(e3?3:(e2?2:(e1?1:0)));
    if (!range) {
        range = e1->get_sort();
    }
    expr_ref result(seq.mk_skolem(s, len, es, range), m);
    if (rw) 
        m_rewrite(result);
    return result;
}

expr_ref skolem::mk_max_unfolding_depth(unsigned depth) { 
    parameter ps[2] = { parameter(m_max_unfolding), parameter(depth) };
    func_decl* f = m.mk_func_decl(seq.get_family_id(), _OP_SEQ_SKOLEM, 2, ps, 0, (sort*const*) nullptr, m.mk_bool_sort());
    return expr_ref(m.mk_const(f), m);
}

expr_ref skolem::mk_length_limit(expr* e, unsigned d) {
    parameter ps[3] = { parameter(m_length_limit), parameter(d), parameter(e) };
    func_decl* f = m.mk_func_decl(seq.get_family_id(), _OP_SEQ_SKOLEM, 3, ps, 0, (sort*const*) nullptr, m.mk_bool_sort());    
    return expr_ref(m.mk_const(f), m);
}

bool skolem::is_length_limit(expr* p, unsigned& lim, expr*& s) const {
    if (!is_length_limit(p))
        return false;
    lim = to_app(p)->get_parameter(1).get_int();
    s = to_expr(to_app(p)->get_parameter(2).get_ast());
    return true;
}


bool skolem::is_skolem(symbol const& s, expr const* e) const {
    return seq.is_skolem(e) && to_app(e)->get_decl()->get_parameter(0).get_symbol() == s;
}

void skolem::decompose(expr* e, expr_ref& head, expr_ref& tail) {
    expr* e1 = nullptr, *e2 = nullptr;
    zstring s;
    rational r;

decompose_main:
    if (seq.str.is_empty(e)) {
        head = seq.str.mk_unit(seq.str.mk_nth_i(e, a.mk_int(0)));
        tail = e;
    }
    else if (seq.str.is_string(e, s)) {
        head = seq.str.mk_unit(seq.str.mk_char(s, 0));
        tail = seq.str.mk_string(s.extract(1, s.length()-1));
    }
    else if (seq.str.is_unit(e)) {
        head = e;        
        tail = seq.str.mk_empty(e->get_sort());
        m_rewrite(head);
    }
    else if (seq.str.is_concat(e, e1, e2) && seq.str.is_empty(e1)) {
        e = e2;
        goto decompose_main;
    }
    else if (seq.str.is_concat(e, e1, e2) && seq.str.is_string(e1, s) && s.length() > 0) {
        head = seq.str.mk_unit(seq.str.mk_char(s, 0));
        tail = seq.str.mk_concat(seq.str.mk_string(s.extract(1, s.length()-1)), e2);
    }
    else if (seq.str.is_concat(e, e1, e2) && seq.str.is_unit(e1)) {
        head = e1;
        tail = e2;
        m_rewrite(head);
        m_rewrite(tail);
    }
    else if (is_skolem(m_tail, e) && a.is_numeral(to_app(e)->get_arg(1), r)) {        
        expr* s = to_app(e)->get_arg(0);        
        expr* idx = a.mk_int(r + 1);
        head = seq.str.mk_unit(seq.str.mk_nth_i(s, idx));
        tail = mk(m_tail, s, idx);
        m_rewrite(head);
    }
    else {
        head = seq.str.mk_unit(seq.str.mk_nth_i(e, a.mk_int(0)));
        tail = mk(m_tail, e, a.mk_int(0));
        m_rewrite(head);
    }
}

bool skolem::is_step(expr* e, expr*& s, expr*& idx, expr*& re, expr*& i, expr*& j, expr*& t) const {
    if (is_step(e)) {
        s    = to_app(e)->get_arg(0);
        idx  = to_app(e)->get_arg(1);
        re   = to_app(e)->get_arg(2);
        i    = to_app(e)->get_arg(3);
        j    = to_app(e)->get_arg(4);
        t    = to_app(e)->get_arg(5);
        return true;
    }
    else {
        return false;
    }
}

bool skolem::is_tail_u(expr* e, expr*& s, unsigned& idx) const {
    expr* i = nullptr;
    rational r;
    return is_tail(e, s, i) && a.is_numeral(i, r) && r.is_unsigned() && (idx = r.get_unsigned(), true);
}

bool skolem::is_tail(expr* e, expr*& s) const {
    expr* i = nullptr;
    return is_tail(e, s, i);
}

bool skolem::is_tail(expr* e, expr*& s, expr*& idx) const {
    return is_tail(e) && (s = to_app(e)->get_arg(0), idx = to_app(e)->get_arg(1), true);
}

bool skolem::is_eq(expr* e, expr*& a, expr*& b) const {
    return is_skolem(m_eq, e) && (a = to_app(e)->get_arg(0), b = to_app(e)->get_arg(1), true);
}

bool skolem::is_pre(expr* e, expr*& s, expr*& i) {
    return is_skolem(m_pre, e) && (s = to_app(e)->get_arg(0), i = to_app(e)->get_arg(1), true);
}

bool skolem::is_post(expr* e, expr*& s, expr*& start) {
    return is_skolem(m_post, e) && (s = to_app(e)->get_arg(0), start = to_app(e)->get_arg(1), true);
}

expr_ref skolem::mk_unit_inv(expr* n) {
    expr* u = nullptr;
    VERIFY(seq.str.is_unit(n, u));
    sort* s = u->get_sort();
    return mk(symbol("seq.unit-inv"), n, s);
}


expr_ref skolem::mk_last(expr* s) {
    zstring str;
    if (seq.str.is_string(s, str) && str.length() > 0) {
        return expr_ref(seq.str.mk_char(str, str.length()-1), m);
    }
    sort* char_sort = nullptr;
    VERIFY(seq.is_seq(s->get_sort(), char_sort));
    return mk(m_seq_last, s, char_sort);
}

expr_ref skolem::mk_first(expr* s) {
    zstring str;
    if (seq.str.is_string(s, str) && str.length() > 0) {
        return expr_ref(seq.str.mk_string(str.extract(0, str.length()-1)), m);
    }
    return mk(m_seq_first, s);
}

expr_ref skolem::mk_step(expr* s, expr* idx, expr* re, unsigned i, unsigned j, expr* t) {
    expr_ref_vector args(m);
    args.push_back(s).push_back(idx).push_back(re);
    args.push_back(a.mk_int(i));
    args.push_back(a.mk_int(j));
    args.push_back(t);
    return expr_ref(seq.mk_skolem(m_aut_step, args.size(), args.data(), m.mk_bool_sort()), m);
}

expr_ref skolem::mk_digit2bv(expr* ch, sort* bv_sort) {
    return mk(symbol("seq.digit2bv"), ch, nullptr, nullptr, nullptr, bv_sort);
}
