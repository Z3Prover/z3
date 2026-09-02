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
        eq_tree::dep_tracker dep = m_ncs[idx].m_dep;
        m_trail.push(vector_erase_trail<str_ncontains>(m_ncs, idx));
        m_ncs.erase(m_ncs.begin() + idx);
        m_ncs.push_back(str_ncontains(new_haystack, needle, dep));
        m_trail.push(push_back_trail<str_ncontains>(m_ncs));
    }

    void ncontains_facet::apply_subst(expr* var, expr_ref_vector const& repl, eq_tree::dep_tracker subst_dep) {
        for (unsigned i = 0; i < m_ncs.size(); ++i) {
            bool touched_h = subst_in_trailed(m_trail, m_ncs, i, &str_ncontains::m_haystack, var, repl);
            bool touched_n = subst_in_trailed(m_trail, m_ncs, i, &str_ncontains::m_needle, var, repl);
            if ((touched_h || touched_n) && subst_dep) {
                m_trail.push(vector_field_trail<str_ncontains, eq_tree::dep_tracker>(m_ncs, i, &str_ncontains::m_dep));
                m_ncs[i].m_dep = m_dm.mk_join(m_ncs[i].m_dep, subst_dep);
            }
        }
    }

    stx::facet_i* ncontains_facet::clone(trail_stack& trail) const {
        ncontains_facet* f = alloc(ncontains_facet, trail, m, u, m_dm);
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
                n.set_conflict(stx::br_plugin_base, nc.m_dep);
                return stx::simplify_result::conflict;
            }

            // Length gate (facet-ncontains.md section 3.3): if h is
            // provably shorter than n, containment is impossible - the
            // obligation is vacuously satisfied. This can only be
            // decided via arith_facet's incremental backend (real
            // str.len reasoning): a haystack/needle *token count* is NOT
            // a sound proxy for actual sequence length here, since a
            // non-constant token is an opaque variable that may denote a
            // string of any length (including longer than any bound
            // implied by token count, or shorter, e.g. epsilon) - unlike
            // eq_facet's constant tokens, which are always exactly one
            // character.
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

            // Recursive prefix-unrolling (facet-ncontains.md section
            // 3.4): try every token-aligned starting position of the
            // needle within the haystack's *current* token list, not
            // just position 0 - since haystack/needle tokens may
            // themselves be unresolved variables, there is in general no
            // single "the" starting position to check; any position
            // whose window fits could be the one where the needle
            // occurs.
            //   - if some position is a *determined* match
            //     (`compare_alignment` returns l_true), the needle
            //     provably occurs somewhere in h - this `not contains`
            //     obligation is UNSAT (conflict), regardless of what any
            //     other position resolves to.
            //   - if EVERY position is a *determined* mismatch (l_false),
            //     the needle provably does not occur anywhere in the
            //     current token list - the obligation is proved and
            //     discharged.
            //   - otherwise some positions are undecided (l_undef: an
            //     unresolved variable token is involved) and none is a
            //     determined match; those undecided positions are left
            //     pending (sound but incomplete, exactly as deq_facet's
            //     own documented incompleteness for un-substituted
            //     variables - a later substitution, broadcast via
            //     apply_subst, may resolve them on a future propagation
            //     round). Any *leading* run of determined-mismatch
            //     positions (before the first undecided one) can still
            //     be safely stripped as progress: no future substitution
            //     can turn an already-determined mismatch into a match,
            //     so it is safe to advance past it (see module comment's
            //     termination argument: the haystack strictly shortens).
            //   - if the haystack currently has fewer tokens than the
            //     needle, there is no complete token-aligned window at
            //     all yet (a haystack variable token may still expand to
            //     supply more tokens via a later Nielsen split): left
            //     pending, no progress made here.
            unsigned h_size = nc.m_haystack.size();
            unsigned n_size = nc.m_needle.size();
            bool has_window = h_size >= n_size;
            unsigned max_pos = has_window ? h_size - n_size : 0;
            bool found_match = false;
            unsigned first_undef_pos = max_pos + 1; // sentinel: "no undef position seen"
            for (unsigned pos = 0; has_window && pos <= max_pos; ++pos) {
                lbool al = compare_alignment(u, nc.m_haystack, pos, nc.m_needle);
                if (al == l_true) {
                    found_match = true;
                    break;
                }
                if (al == l_undef && first_undef_pos > max_pos) {
                    first_undef_pos = pos;
                    // keep scanning later positions: a later position
                    // might still be a determined match (conflict) even
                    // though this one is undecided.
                }
            }
            if (found_match) {
                n.set_conflict(stx::br_plugin_base, nc.m_dep);
                return stx::simplify_result::conflict;
            }
            if (has_window && first_undef_pos > max_pos) {
                // every position is a determined mismatch: the needle
                // cannot occur anywhere in the current haystack.
                f.remove(i);
                changed = true;
                continue;
            }
            if (has_window && first_undef_pos > 0) {
                // strip the leading run of determined-mismatch positions.
                expr_ref_vector tail(m);
                tail.append(h_size - first_undef_pos, nc.m_haystack.data() + first_undef_pos);
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
