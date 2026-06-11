/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_regex_bisim.cpp

Abstract:

    See seq_regex_bisim.h.

Author:

    Margus Veanes   (veanes)
    Nikolaj Bjorner (nbjorner)
    
--*/

#include "ast/rewriter/seq_regex_bisim.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/ast_pp.h"
#include "ast/ast_util.h"
#include "ast/for_each_expr.h"

namespace seq {

    regex_bisim::regex_bisim(seq_rewriter& rw):
        m(rw.m()),
        m_rw(rw),
        m_util(rw.u()),
        m_pinned(m),
        m_worklist(m) {
    }

    void regex_bisim::reset() {
        m_uf.reset();
        m_node_of.reset();
        m_pinned.reset();
        m_worklist.reset();
        m_steps = 0;
    }

    /*
       Map an expression to a union-find node, allocating a fresh node on
       first encounter.
    */
    unsigned regex_bisim::node_of(expr* r) {
        unsigned id = 0;
        if (m_node_of.find(r, id))
            return id;
        id = m_uf.mk_var();
        m_node_of.insert(r, id);
        m_pinned.push_back(r);
        return id;
    }

    /*
       Compute a definite nullability answer for r.
       If the seq_rewriter is unable to produce a literal true/false (for
       example because r contains an uninterpreted symbol), return l_undef.
    */
    lbool regex_bisim::nullability(expr* r) {
        expr_ref n = m_rw.is_nullable(r);
        if (m.is_true(n))
            return l_true;
        if (m.is_false(n))
            return l_false;
        return l_undef;
    }

    /*
       Test whether a regex expression is a kind that the bisimulation
       procedure can reason about. We require it to be a syntactic ground
       term (no free variables) and that its info reports min_length info
       (which implies that it parses cleanly as a regex constructor).
    */
    bool regex_bisim::is_supported(expr* r) {
        if (!m_util.is_re(r))
            return false;
        if (!m_util.re.get_info(r).is_known())
            return false;
        // Reject regexes mentioning free variables; the symbolic
        // derivative engine introduces (:var 0) only after we call it
        // ourselves, so any pre-existing variable would be a free var.
        return is_ground(r);
    }

    /*
       Collect the leaves of a t-regex der (an ITE / antimirov union /
       union-tree with regex leaves) into the output vector. Empty
       (re.empty) leaves are dropped.

       Returns false if we encountered an unexpected node (e.g. a free
       variable creeping in) — in that case the caller should bail out.
    */
    bool regex_bisim::collect_leaves(expr* der, expr_ref_vector& leaves) {
        ptr_vector<expr> work;
        obj_hashtable<expr> seen;
        work.push_back(der);
        seen.insert(der);
        while (!work.empty()) {
            expr* e = work.back();
            work.pop_back();
            expr* c = nullptr, * t = nullptr, * f = nullptr;
            if (m.is_ite(e, c, t, f) ||
                m_util.re.is_union(e, t, f) ||
                m_util.re.is_antimirov_union(e, t, f)) {
                if (seen.insert_if_not_there(t))
                    work.push_back(t);
                if (seen.insert_if_not_there(f))
                    work.push_back(f);
                continue;
            }
            if (m_util.re.is_empty(e))
                continue;
            if (!m_util.is_re(e))
                return false;
            leaves.push_back(e);
        }
        return true;
    }

    /*
       Fast inequivalence check based on the get_info().classical flag.

       Invariant: if r is well-formed and get_info(r).classical is true,
       then L(r) is non-empty. The flag is set for regexes built only
       from str.to_re, re.all, union, concat, star, plus, opt, loop;
       it excludes complement, intersection, diff, xor, and the empty
       regex.

       A bare regex leaf l (i.e. not a XOR pair) represents the implicit
       pair (empty XOR l). If l is classical, L(l) is non-empty so the
       pair is non-empty: the original two regexes have a distinguishing
       prefix and are inequivalent.

       For an XOR leaf xor(a, b): if both a and b are classical and have
       different min_length, then the shortest word of one is not in the
       other, so the pair is non-empty and we can short-circuit. (The
       case a == b syntactically is already handled by mk_re_xor0.)

       Returns true if the leaf proves inequivalence; false if no
       conclusion can be drawn.
    */
    bool regex_bisim::classical_distinguishing(expr* l) {
        expr* a = nullptr, * b = nullptr;
        if (m_util.re.is_xor(l, a, b)) {
            auto ia = m_util.re.get_info(a);
            auto ib = m_util.re.get_info(b);
            if (ia.is_known() && ib.is_known() &&
                ia.classical && ib.classical &&
                ia.min_length != ib.min_length)
                return true;
            return false;
        }
        if (m_util.re.is_empty(l))
            return false;
        auto info = m_util.re.get_info(l);
        return info.is_known() && info.classical;
    }

    /*
       Merge the two sides of the XOR pair, returning true if a fresh
       merge happened (i.e. the pair must still be processed) and false
       if the two sides were already in the same union-find class.

       For non-XOR leaves we treat the leaf l as the pair (empty XOR l).
    */
    bool regex_bisim::merge_leaf(expr* leaf) {
        expr* a = nullptr, * b = nullptr;
        if (!m_util.re.is_xor(leaf, a, b)) {
            a = m_util.re.mk_empty(leaf->get_sort());
            b = leaf;
            m_pinned.push_back(a);
        }
        unsigned ia = node_of(a);
        unsigned ib = node_of(b);
        if (m_uf.find(ia) == m_uf.find(ib))
            return false;
        m_uf.merge(ia, ib);
        return true;
    }

    /*
       Decide equivalence by bisimulation on D(p XOR q).
    */
    lbool regex_bisim::are_equivalent(expr* p, expr* q) {
        return are_equivalent_core(p, q);
    }

    lbool regex_bisim::are_equivalent_core(expr* p, expr* q) {
        if (!is_supported(p) || !is_supported(q))
            return l_undef;
        if (p == q)
            return l_true;

        reset();

        // Build the initial pair r0 = p XOR q applying the structural
        // XOR rewrites (r XOR r = empty, AC normalisation, etc.).
        expr_ref r0 = m_rw.mk_re_xor_simplified(p, q);

        // If r0 simplified to empty, the two regexes are equivalent.
        if (m_util.re.is_empty(r0))
            return l_true;

        lbool n0 = nullability(r0);
        if (n0 == l_true)
            return l_false; // distinguishing empty word
        if (n0 == l_undef)
            return l_undef;

        // Classical-leaf shortcut applied to r0 (covers the case where
        // mk_re_xor_simplified collapsed p XOR q to a bare classical
        // residual, e.g. when one side reduced to empty).
        if (classical_distinguishing(r0))
            return l_false;

        if (!merge_leaf(r0))
            return l_true; // already merged: trivially equivalent
        m_worklist.push_back(r0);

        while (!m_worklist.empty()) {
            if (++m_steps > m_step_bound)
                return l_undef;

            expr_ref r(m_worklist.back(), m);
            m_worklist.pop_back();

            // Compute the symbolic derivative wrt the canonical variable
            // (:var 0). The result is a transition regex (ITE tree) whose
            // leaves are regex expressions. We use the classical Brzozowski
            // entry point so the derivative stays as a single TRegex and
            // does not lift unions to the top via antimirov nodes — this
            // preserves the XOR-pair invariant the bisimulation relies on.
            expr_ref d(m_rw.mk_brz_derivative(r), m);
            expr_ref_vector leaves(m);
            if (!collect_leaves(d, leaves))
                return l_undef;

            // First pass: check for any nullable leaf (definitive
            // distinguishing empty-continuation word) or any classically
            // non-empty leaf (definitive distinguishing non-empty prefix).
            for (expr* l : leaves) {
                lbool nl = nullability(l);
                if (nl == l_true)
                    return l_false;
                if (nl == l_undef)
                    return l_undef;
                if (classical_distinguishing(l))
                    return l_false;
            }

            // Second pass: merge each leaf into the union-find; new
            // merges go onto the worklist.
            for (expr* l : leaves) {
                if (merge_leaf(l)) {
                    m_pinned.push_back(l);
                    m_worklist.push_back(l);
                }
            }
        }
        return l_true;
    }
}
