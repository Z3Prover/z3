/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_ssnf.cpp

Abstract:

    Strong star normal form (SSNF) for regular expressions.

    Two mutually recursive maps, following Bruggemann-Klein and the "strong"
    variant of Gruber and Gulan:

      ssnf(r)   language-preserving; the only structural changes are that a
                star body is replaced by its circ, and that an epsilon
                alternative is dropped from a union whose other side is
                nullable (equivalently: r? collapses to r when r is nullable)

      circ(r)   epsilon-free where a rule applies, and only ever used under a
                star, where the contract is L(circ(r)*) = L(r*):
                  eps, empty      -> empty            (empty* = eps* = {eps})
                  Sigma*          -> Sigma
                  r*, r+, r?      -> circ(r)
                  r1 | r2         -> circ(r1) | circ(r2)
                  r1 . r2         -> circ(r1) | circ(r2)   if both nullable
                  r{lo,hi}        -> circ(r)               if the loop is nullable
                  anything else   -> unchanged

Author:

    Clemens Eisenhofer 2026-08-31

--*/

#include "ast/rewriter/seq_ssnf.h"

// Rebuild r with ssnf applied to each of its regex-sorted arguments.  Covers
// concat, intersection, difference, xor, complement, reverse, loop, derivative
// and ite uniformly; arguments of other sorts (the sequence of str.to_re, the
// bounds of a loop, the character of a derivative) are left alone.
expr* seq_ssnf::rebuild(expr* r, unsigned depth) {
    if (!is_app(r))
        return r;
    app* a = to_app(r);
    ptr_buffer<expr> args;
    bool change = false;
    for (expr* arg : *a) {
        expr* arg1 = arg;
        if (m_seq.is_re(arg))
            arg1 = ssnf_rec(arg, depth + 1);
        change |= arg1 != arg;
        args.push_back(arg1);
    }
    if (!change)
        return r;
    return m.mk_app(a->get_decl(), args.size(), args.data());
}

expr* seq_ssnf::ssnf_rec(expr* r, unsigned depth) {
    if (depth >= max_depth)
        return r;
    expr* res = nullptr;
    if (m_ssnf.find(r, res))
        return res;

    expr* a = nullptr, *b = nullptr;
    res = r;
    if (re().is_star(r, a)) {
        expr* a1 = circ(ssnf_rec(a, depth + 1), depth + 1);
        if (a1 != a)
            res = re().mk_star(a1);
    }
    else if (re().is_plus(r, a)) {
        expr* a1 = ssnf_rec(a, depth + 1);
        // r+ = r* when r is nullable
        if (nullable(a1) == l_true)
            res = re().mk_star(circ(a1, depth + 1));
        else if (a1 != a)
            res = re().mk_plus(a1);
    }
    else if (re().is_opt(r, a)) {
        expr* a1 = ssnf_rec(a, depth + 1);
        if (nullable(a1) == l_true)
            res = a1;
        else if (a1 != a)
            res = re().mk_opt(a1);
    }
    else if (re().is_union(r, a, b)) {
        expr* a1 = ssnf_rec(a, depth + 1);
        expr* b1 = ssnf_rec(b, depth + 1);
        if (re().is_epsilon(a1) && nullable(b1) == l_true)
            res = b1;
        else if (re().is_epsilon(b1) && nullable(a1) == l_true)
            res = a1;
        else if (a1 != a || b1 != b)
            res = re().mk_union(a1, b1);
    }
    else
        res = rebuild(r, depth);

    m_ssnf.insert(r, res);
    m_pin.push_back(r);
    m_pin.push_back(res);
    return res;
}

expr* seq_ssnf::circ(expr* r, unsigned depth) {
    // an epsilon-free expression is its own circ
    if (nullable(r) == l_false || depth >= max_depth)
        return r;
    expr* res = nullptr;
    if (m_circ.find(r, res))
        return res;

    expr* a = nullptr, *b = nullptr;
    unsigned lo = 0, hi = 0;
    res = r;
    if (re().is_epsilon(r) || re().is_empty(r))
        res = re().mk_empty(r->get_sort());
    else if (re().is_full_seq(r))
        res = re().mk_full_char(r->get_sort());
    else if (re().is_star(r, a) || re().is_plus(r, a) || re().is_opt(r, a))
        res = circ(a, depth + 1);
    else if (re().is_union(r, a, b))
        res = re().mk_union(circ(a, depth + 1), circ(b, depth + 1));
    else if (re().is_concat(r, a, b) && nullable(a) == l_true && nullable(b) == l_true)
        res = re().mk_union(circ(a, depth + 1), circ(b, depth + 1));
    else if (re().is_loop(r, a, lo, hi)) {
        // r{lo,hi}* = r* as soon as one iteration of r is available and the
        // loop can be skipped, i.e. lo = 0 or r itself is nullable
        if (hi == 0)
            res = re().mk_empty(r->get_sort());
        else if (lo == 0 || nullable(a) == l_true)
            res = circ(a, depth + 1);
    }
    else if (re().is_loop(r, a, lo)) {
        if (lo == 0 || nullable(a) == l_true)
            res = circ(a, depth + 1);
    }

    m_circ.insert(r, res);
    m_pin.push_back(r);
    m_pin.push_back(res);
    return res;
}
