/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    seq_simplifier.cpp

Abstract:

    Global simplifier for sequences

Author:

    Nikolaj Bjorner (nbjorner) 2023-03-12.

--*/


#include "ast/simplifiers/seq_simplifier.h"

//
// if x, y always are in pattern .. ++ x ++ y ++ .. -> z
// x ++ a ++ y = s, where s containing a, x, y are unique -> true
// Parikh pre-processing based on regex membership constraints and equations
// Sequencing abstractions:
// example   x in a*, y in b*, z = (ba)+, xy = z
//   last(xy) = a => first(xy) = a
//   last(z)  = a
//   first(z) = b
// 
// Lookahead
//   to help with sequence abstractions?
//   
// solve for queues:
//   X   = ABC
//   XX  = AABBCC
//   XXX = AAABBBCCC
//   B   = bB'
//   C   = cC'
//   XX  = ABCABC
//   |A| = |C| => ABC = AAB = BCC
//   

void seq_simplifier::reduce() {
    if (!m_seq.has_seq())
        return;
    elim_unconstrained elim(m, m_fmls);
    elim.init_nodes();
    eliminate(elim);
}

bool seq_simplifier::invert(elim_unconstrained& elim, app* t, expr_ref& r) {
    if (!m_seq.str.is_concat(t))
        return false;


    auto is_valid_parent = [&](expr* p) {
        return elim.get_node(p).m_refcount > 0 && elim.get_node(p).m_term == elim.get_node(p).m_orig;
    };

    expr* first = nullptr, *second = nullptr;
    expr* a, *b, *c, *d, *e;
    for (expr* p : elim.get_node(t).m_parents) {
        if (!is_valid_parent(p))
            continue;        
        if (!m_seq.str.is_concat(p, a, b))
            return false;
        if (!m_seq.str.is_concat(b, c, d))
            c = b;
        if (first && (first != a || second != c))
            return false;
        first  = a;
        second = c;
        // parents of b are all of the form (seq.++ a b)
        for (expr* q : elim.get_node(b).m_parents) {
            if (!is_valid_parent(q))
                continue;
            if (!m_seq.str.is_concat(q, d, e))
                return false;
            if (e != b || d != a)
                return false;
        }
    }

    if (!first)
        return false;

    expr* x = nullptr;
    // replace p := a ++ b ++ c by x ++ c
    for (expr* p : elim.get_node(t).m_parents) {
        if (!is_valid_parent(p))
            continue;        
        VERIFY(m_seq.str.is_concat(p, a, b));
        if (m_seq.str.is_concat(b, c, d))
            r = m_seq.str.mk_concat(x, d);
        else
            r = x;
        // p := r
    }
    
    return false;
}

void seq_simplifier::eliminate(elim_unconstrained& elim) {
#if 0
    while (!elim.m_heap.empty()) {
        expr_ref r(m);
        int v = elim.m_heap.erase_min();
        node& n = elim.get_node(v);
        if (n.m_refcount == 0)
            continue;
        if (n.m_parents.empty()) {
            n.m_refcount = 0;
            continue;
        }
        expr* e = elim.get_parent(v);
        IF_VERBOSE(11, for (expr* p : n.m_parents) verbose_stream() << "parent " << mk_bounded_pp(p, m) << " @ " << get_node(p).m_refcount << "\n";);
        if (!e || !is_app(e) || !is_ground(e)) {
            n.m_refcount = 0;
            continue;
        }
        app* t = to_app(e);
        bool inverted = invert(elim, t, r);
        n.m_refcount = 0;
        if (!inverted) {
            IF_VERBOSE(11, verbose_stream() << "not inverted " << mk_bounded_pp(e, m) << "\n");
            continue;
        }
        
        TRACE("elim_unconstrained", tout << mk_pp(t, m) << " -> " << r << "\n");
        SASSERT(r->get_sort() == t->get_sort());
        elim.m_stats.m_num_eliminated++;
        elim.m_trail.push_back(r);
        SASSERT(r);
        elim.gc(e);
        elim.invalidate_parents(e);
        elim.freeze_rec(r);
        
        elim.m_root.setx(r->get_id(), e->get_id(), UINT_MAX);
        elim.get_node(e).m_term = r;
        elim.get_node(e).m_proof = pr;
        elim.get_node(e).m_refcount++;
        IF_VERBOSE(11, verbose_stream() << mk_bounded_pp(e, m) << "\n");
        SASSERT(!elim.m_heap.contains(root(e)));
        if (is_uninterp_const(r))
            elim.m_heap.insert(root(e));
        else
            elim.m_created_compound = true;

        IF_VERBOSE(11, verbose_stream() << mk_bounded_pp(get_node(v).m_orig, m) << " " << mk_bounded_pp(t, m) << " -> " << r << " " << elim.get_node(e).m_refcount << "\n";);

    }

#endif
}

