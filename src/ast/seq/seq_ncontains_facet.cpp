/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_ncontains_facet.cpp

Abstract:

    See seq_ncontains_facet.h.

Author:

    Nikolaj Bjorner (nbjorner) 2026

--*/
#include "ast/seq/seq_ncontains_facet.h"
#include <algorithm>

namespace seq {

    static int cmp_expr_ref_vectors(expr_ref_vector const& a, expr_ref_vector const& b) {
        unsigned n = std::min(a.size(), b.size());
        for (unsigned i = 0; i < n; ++i) {
            unsigned ida = a[i]->get_id(), idb = b[i]->get_id();
            if (ida != idb)
                return ida < idb ? -1 : 1;
        }
        if (a.size() != b.size())
            return a.size() < b.size() ? -1 : 1;
        return 0;
    }

    bool str_ncontains::operator<(str_ncontains const& other) const {
        int c = cmp_expr_ref_vectors(m_haystack, other.m_haystack);
        if (c != 0)
            return c < 0;
        return cmp_expr_ref_vectors(m_needle, other.m_needle) < 0;
    }

    bool str_ncontains::operator==(str_ncontains const& other) const {
        return cmp_expr_ref_vectors(m_haystack, other.m_haystack) == 0 &&
               cmp_expr_ref_vectors(m_needle, other.m_needle) == 0;
    }

    void ncontains_facet::remove(unsigned idx) {
        m_trail.push(vector_erase_trail<str_ncontains>(m_ncs, idx));
        m_ncs.erase(m_ncs.begin() + idx);
    }

    void ncontains_facet::replace_with_tail(unsigned idx, expr_ref_vector const& new_haystack) {
        expr_ref_vector needle(m_ncs[idx].m_needle);
        m_trail.push(vector_erase_trail<str_ncontains>(m_ncs, idx));
        m_ncs.erase(m_ncs.begin() + idx);
        m_ncs.push_back(str_ncontains(new_haystack, needle));
        m_trail.push(push_back_trail<str_ncontains>(m_ncs));
    }

    void ncontains_facet::apply_subst(expr* var, expr_ref_vector const& repl) {
        for (unsigned i = 0; i < m_ncs.size(); ++i) {
            subst_in_trailed(m_trail, m_ncs, i, &str_ncontains::m_haystack, var, repl);
            subst_in_trailed(m_trail, m_ncs, i, &str_ncontains::m_needle, var, repl);
        }
    }

    stx::facet_i* ncontains_facet::clone(trail_stack& trail) const {
        ncontains_facet* f = alloc(ncontains_facet, trail, m, u);
        f->m_ncs.append(m_ncs);
        return f;
    }

    unsigned ncontains_facet::hash() const {
        // Order-independent, same rationale as eq_facet::hash.
        unsigned h = m_ncs.size() * 40503u;
        for (auto const& nc : m_ncs) {
            unsigned nh = 1;
            for (expr* t : nc.m_haystack) nh = combine_hash(nh, t->get_id());
            nh = combine_hash(nh, 0xc2b2ae35u);
            for (expr* t : nc.m_needle) nh = combine_hash(nh, t->get_id());
            h += nh;
        }
        return h ? h : 1;
    }

    bool ncontains_facet::similar(facet_i const& other) const {
        auto const& o = static_cast<ncontains_facet const&>(other);
        if (m_ncs.size() != o.m_ncs.size())
            return false;
        vector<str_ncontains> a = m_ncs, b = o.m_ncs;
        std::sort(a.begin(), a.end());
        std::sort(b.begin(), b.end());
        for (unsigned i = 0; i < a.size(); ++i)
            if (!(a[i] == b[i]))
                return false;
        return true;
    }

    // Build a str.++ chain expr from a token list, for querying
    // arith_facet's length-gate (`u.str.mk_length` needs an actual
    // sequence-sorted expr, not a token vector).
    static expr* tokens_to_expr(seq_util& u, ast_manager& m, expr_ref_vector const& ts) {
        if (ts.empty())
            return u.str.mk_empty(u.str.mk_string(zstring())->get_sort());
        return u.str.mk_concat(ts.size(), ts.data(), ts[0]->get_sort());
    }

    // Compare `h`'s tokens at [pos, pos+n.size()) against `n`, token by
    // token. Returns `l_true` if every position is a resolved match
    // (either identical pointers, i.e. the same variable/constant token,
    // or two distinct-but-equal-value constants - which cannot happen
    // here since string constants are interned, so pointer equality
    // already captures value equality), `l_false` if some position is a
    // *determined* mismatch (both tokens are resolved constants and
    // different), and `l_undef` if the alignment cannot yet be decided
    // (some position pairs an unresolved variable with anything, so a
    // future substitution could still make it match or not).
    static lbool compare_alignment(seq_util& u, expr_ref_vector const& h, unsigned pos, expr_ref_vector const& n) {
        bool undef = false;
        for (unsigned k = 0; k < n.size(); ++k) {
            expr* ht = h.get(pos + k);
            expr* nt = n.get(k);
            if (ht == nt)
                continue; // identical token (same variable, or same interned constant)
            if (is_const_token(u, ht) && is_const_token(u, nt))
                return l_false; // distinct resolved constants: determined mismatch
            undef = true; // at least one side is an unresolved variable
        }
        return undef ? l_undef : l_true;
    }

    stx::simplify_result ncontains_propagation::propagate(eq_tree::node& n) {
        auto& f = n.facet_as<ncontains_facet>(m_ncontains_id);
        auto& af = n.facet_as<arith_facet>(m_arith_id);

        bool changed = false;
        for (unsigned i = 0; i < f.ncontains().size(); ) {
            str_ncontains const& nc = f.ncontains()[i];

            // Trivial conflict: an empty needle is always contained.
            if (nc.m_needle.empty()) {
                n.set_conflict(stx::br_plugin_base, nullptr);
                return stx::simplify_result::conflict;
            }

            // Length gate (facet-ncontains.md section 3.3): if h is
            // provably shorter than n, containment is impossible - the
            // obligation is vacuously satisfied. A cheap syntactic
            // special case (h's *token count* already less than n's, a
            // lower bound on len(h) - len(n) that needs no solver query)
            // is checked first; the general case falls through to
            // arith_facet's incremental backend.
            if (nc.m_haystack.size() < nc.m_needle.size()) {
                f.remove(i);
                changed = true;
                continue;
            }

            expr* h_expr = tokens_to_expr(u, m, nc.m_haystack);
            expr* n_expr = tokens_to_expr(u, m, nc.m_needle);
            expr_ref len_h(u.str.mk_length(h_expr), m);
            expr_ref len_n(u.str.mk_length(n_expr), m);
            expr_ref gate(m.mk_not(a.mk_le(len_n, len_h)), m); // len(h) < len(n)

            if (af.implies(gate) == l_true) {
                // len(h) < len(n): n cannot possibly occur in h - the
                // obligation is vacuously satisfied.
                f.remove(i);
                changed = true;
                continue;
            }

            // Recursive prefix-unrolling (facet-ncontains.md section 3.4),
            // implemented here as deterministic propagation rather than a
            // nondeterministic split: at each candidate starting position
            // of an occurrence, `compare_alignment` either determines the
            // needle can never start there (l_false - safe to strip that
            // one leading haystack token and recurse, i.e. progress with
            // no branching) or determines it definitely DOES start there
            // (l_true - the needle provably occurs in h, so this
            // `not contains` obligation is UNSAT) or cannot yet decide
            // (l_undef - some leading token is an unresolved variable;
            // left pending, exactly as deq_facet's own documented
            // incompleteness for un-substituted variables. See module
            // comment's scope note: eq_facet's Nielsen splits will keep
            // narrowing those variables on later propagation rounds via
            // `apply_subst`, at which point this check re-runs and may
            // finally decide the alignment).
            lbool al = compare_alignment(u, nc.m_haystack, 0, nc.m_needle);
            if (al == l_true) {
                n.set_conflict(stx::br_plugin_base, nullptr);
                return stx::simplify_result::conflict;
            }
            if (al == l_false) {
                expr_ref_vector tail(m);
                tail.append(nc.m_haystack.size() - 1, nc.m_haystack.data() + 1);
                f.replace_with_tail(i, tail);
                changed = true;
                continue; // re-examine the same obligation at index i (now shortened)
            }
            ++i;
        }
        if (f.is_satisfied())
            return stx::simplify_result::satisfied;
        return changed ? stx::simplify_result::proceed : stx::simplify_result::noop;
    }

} // namespace seq
