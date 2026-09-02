/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_charclass.cpp

Abstract:

    Collapse A & ~C into a character class when A is one.  See seq_charclass.h.

Author:

    Clemens Eisenhofer 2026-08-31

--*/

#include "ast/rewriter/seq_charclass.h"
#include "ast/rewriter/seq_range_collapse.h"

bool seq_charclass::charset(expr* r, seq::range_predicate& out, unsigned depth) const {
    if (depth >= max_depth)
        return false;
    if (seq::regex_to_range_predicate(m_seq, r, out))
        return true;

    // A one-character string literal is a character class; the fragment above
    // does not recognize str.to_re at all, and this is the form the benchmarks
    // use.  A literal of any other length is not (the empty word and words of
    // length two or more are not characters).
    expr* body = nullptr;
    zstring s;
    if (re().is_to_re(r, body) && m_seq.str.is_string(body, s)) {
        if (s.length() != 1)
            return false;
        out = seq::range_predicate::singleton(s[0], m_seq.max_char());
        return true;
    }

    // regex_to_range_predicate gives up on the whole term as soon as one leaf
    // is outside its fragment, so the boolean cases are re-tried here with the
    // extended leaf reading.
    expr* a = nullptr, *b = nullptr;
    seq::range_predicate pa(m_seq.max_char()), pb(m_seq.max_char());
    if (re().is_union(r, a, b)) {
        if (!charset(a, pa, depth + 1) || !charset(b, pb, depth + 1))
            return false;
        out = pa | pb;
        return true;
    }
    if (re().is_intersection(r, a, b)) {
        if (!charset(a, pa, depth + 1) || !charset(b, pb, depth + 1))
            return false;
        out = pa & pb;
        return true;
    }
    if (re().is_diff(r, a, b)) {
        if (!charset(a, pa, depth + 1) || !charset(b, pb, depth + 1))
            return false;
        out = pa - pb;
        return true;
    }
    return false;
}

bool seq_charclass::collapse(expr* a, expr* c, expr_ref& out) const {
    sort* seq_sort = nullptr;
    if (!m_seq.is_re(a->get_sort(), seq_sort))
        return false;
    seq::range_predicate pa(m_seq.max_char());
    if (!charset(a, pa, 0))
        return false;

    seq::range_predicate pc(m_seq.max_char());
    if (charset(c, pc, 0)) {
        out = seq::range_predicate_to_regex(m_seq, pa - pc, seq_sort);
        return true;
    }
    // c holds no word of length one, so it removes nothing from a subset of Σ
    const seq_util::rex::info info = re().get_info(c);
    if (info.is_known() && (info.min_length > 1 || info.max_length == 0)) {
        out = seq::range_predicate_to_regex(m_seq, pa, seq_sort);
        return true;
    }
    return false;
}

expr* seq_charclass::rec(expr* r, unsigned depth) {
    if (depth >= max_depth)
        return r;
    expr* res = nullptr;
    if (m_cache.find(r, res))
        return res;

    res = r;
    if (is_app(r)) {
        // rewrite the regex-sorted arguments first, so a collapse enabled by an
        // inner one is seen here
        app* t = to_app(r);
        ptr_buffer<expr> args;
        bool change = false;
        for (expr* arg : *t) {
            expr* arg1 = arg;
            if (m_seq.is_re(arg))
                arg1 = rec(arg, depth + 1);
            change |= arg1 != arg;
            args.push_back(arg1);
        }
        if (change)
            res = m.mk_app(t->get_decl(), args.size(), args.data());

        expr* a = nullptr, *b = nullptr, *c = nullptr;
        expr_ref out(m);
        if (re().is_intersection(res, a, b)
            && ((re().is_complement(b, c) && collapse(a, c, out))
                || (re().is_complement(a, c) && collapse(b, c, out)))) {
            // pin before `out` goes out of scope: it holds the only reference
            m_pin.push_back(out);
            res = out.get();
        }
    }

    m_cache.insert(r, res);
    m_pin.push_back(r);
    m_pin.push_back(res);
    return res;
}
