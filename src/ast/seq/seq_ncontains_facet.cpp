/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_ncontains_facet.cpp

Abstract:

    See seq_ncontains_facet.h.

Author:

    Nikolaj Bjorner (nbjorner) 2026
    Clemens Eisenhofer 2026
    Margus Veanes 2026

--*/
#include "ast/seq/seq_ncontains_facet.h"
#include "ast/seq/seq_solver_facet_i.h"
#include "ast/ast_pp.h"
#include <algorithm>

namespace seq {

    void ncontains_facet::advance_qhead(unsigned head) {
        m_trail.push(value_trail<unsigned>(m_qhead));
        m_qhead = head;
    }

    void ncontains_facet::rewind_qhead(unsigned idx) {
        if (idx < m_qhead)
            advance_qhead(idx);
    }

    void ncontains_facet::remove(unsigned idx) {
        m_trail.push(vector_field_trail<str_ncontains, bool>(m_ncs, idx, &str_ncontains::m_active));
        m_ncs[idx].m_active = false;
    }

    void ncontains_facet::replace_with_tail(unsigned idx, expr_ref_vector const& new_haystack) {
        expr_ref_vector needle(m_ncs[idx].m_needle);
        eq_tree::dep_tracker dep = m_ncs[idx].m_dep;
        m_trail.push(vector_field_trail<str_ncontains, bool>(m_ncs, idx, &str_ncontains::m_active));
        m_ncs[idx].m_active = false;
        m_ncs.push_back(str_ncontains(new_haystack, needle, dep));
        m_trail.push(push_back_trail<str_ncontains>(m_ncs));
    }

    void ncontains_facet::apply_subst(expr* var, expr_ref_vector const& repl, eq_tree::dep_tracker subst_dep) {
        for (unsigned i = 0; i < m_ncs.size(); ++i) {
            if (!m_ncs[i].active())
                continue;
            bool touched_h = subst_in_trailed(m_trail, m_ncs, i, &str_ncontains::m_haystack, var, repl);
            bool touched_n = subst_in_trailed(m_trail, m_ncs, i, &str_ncontains::m_needle, var, repl);
            if (touched_h || touched_n) {
                if (subst_dep) {
                    m_trail.push(vector_field_trail<str_ncontains, eq_tree::dep_tracker>(m_ncs, i, &str_ncontains::m_dep));
                    m_ncs[i].m_dep = m_dm.mk_join(m_ncs[i].m_dep, subst_dep);
                }
                // A substitution may invalidate a "no further progress
                // possible" verdict ncontains_propagation reached for
                // this obligation in an earlier round (e.g. an
                // undecided position may now resolve), so make sure it
                // is re-examined next round even if qhead had already
                // advanced past it.
                rewind_qhead(i);
            }
        }
    }

    stx::facet_i* ncontains_facet::clone(trail_stack& trail) const {
        ncontains_facet* f = alloc(ncontains_facet, trail, m, u, m_dm);
        f->m_ncs.append(m_ncs);
        f->m_qhead = m_qhead;
        return f;
    }

    std::ostream& ncontains_facet::display(std::ostream& out) const {
        out << "ncontains_facet: " << m_ncs.size() << " obligation(s), qhead=" << m_qhead << "\n";
        for (auto const& nc : m_ncs) {
            if (!nc.active())
                continue;
            out << "  not-contains(";
            for (expr* t : nc.m_haystack) out << mk_pp(t, m) << " ";
            out << ", ";
            for (expr* t : nc.m_needle) out << mk_pp(t, m) << " ";
            out << ")\n";
        }
        return out;
    }

    // Build a str.++ chain expr from a token list, for querying
    // solver_facet's length-gate (`u.str.mk_length` needs an actual
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
    static lbool compare_alignment(seq_util& u, ast_manager& m, expr_ref_vector const& h, unsigned pos, expr_ref_vector const& n) {
        bool undef = false;
        for (unsigned k = 0; k < n.size(); ++k) {
            expr* ht = h.get(pos + k);
            expr* nt = n.get(k);
            if (ht == nt)
                continue; // identical token (same variable, or same interned constant)
            if (u.str.is_unit(ht) && u.str.is_unit(nt) && m.are_distinct(ht, nt))
                return l_false; // distinct resolved constants: determined mismatch
            undef = true; // at least one side is an unresolved variable
        }
        return undef ? l_undef : l_true;
    }

    stx::simplify_result ncontains_propagation::propagate(eq_tree::node& n) {
        auto ac = get_ambient(n);
        auto& f = ac.ncontains_facet_ref();
        auto& af = ac.arith_facet_ref();
        m_stats.m_num_propagate++;

        bool changed = false;
        // Incremental scan: only [qhead, ncontains().size()) is examined
        // this round (mirrors req_facet's own m_qhead convention). An
        // obligation that becomes inactive (remove()/replace_with_tail())
        // is simply skipped from here on; replace_with_tail's shortened
        // replacement is appended past the current scan position, so it
        // is picked up later in this same forward scan without needing
        // to revisit `head`. apply_subst rewinds qhead when it touches
        // an already-scanned obligation, so this loop never needs to
        // look behind qhead on its own.
        unsigned head = f.qhead();
        while (head < f.ncontains().size()) {
            if (!f.ncontains()[head].active()) {
                ++head;
                continue;
            }
            str_ncontains const& nc = f.ncontains()[head];

            // Trivial conflict: an empty needle is always contained.
            if (nc.m_needle.empty()) {
                n.set_conflict(stx::br_plugin_base, nc.m_dep);
                return stx::simplify_result::conflict;
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
                lbool al = compare_alignment(u, m, nc.m_haystack, pos, nc.m_needle);
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
                f.remove(head);
                changed = true;
                ++head;
                continue;
            }
            if (has_window && first_undef_pos > 0) {
                // strip the leading run of determined-mismatch positions.
                expr_ref_vector tail(m);
                tail.append(h_size - first_undef_pos, nc.m_haystack.data() + first_undef_pos);
                f.replace_with_tail(head, tail);
                changed = true;
                ++head; // the shortened replacement, appended past `head`,
                        // is picked up later in this same forward scan.
                continue;
            }

            // Length gate (facet-ncontains.md section 3.3): only reached
            // once the cheap syntactic scan above found no determined
            // match/mismatch/progress. If h is provably shorter than n,
            // containment is impossible - the obligation is vacuously
            // satisfied. This can only be decided via solver_facet's
            // incremental backend (real str.len reasoning): a
            // haystack/needle *token count* is NOT a sound proxy for
            // actual sequence length here, since a non-constant token is
            // an opaque variable that may denote a string of any length
            // (including longer than any bound implied by token count,
            // or shorter, e.g. epsilon) - unlike eq_facet's constant
            // tokens, which are always exactly one character. Checked
            // last since it invokes the (comparatively expensive)
            // incremental arithmetic solver.
            expr* h_expr = tokens_to_expr(u, m, nc.m_haystack);
            expr* n_expr = tokens_to_expr(u, m, nc.m_needle);
            expr_ref len_h(u.str.mk_length(h_expr), m);
            expr_ref len_n(u.str.mk_length(n_expr), m);
            expr_ref gate(m.mk_not(a.mk_le(len_n, len_h)), m); // len(h) < len(n)

            if (af.implies(gate) == l_true) {
                // len(h) < len(n): n cannot possibly occur in h - the
                // obligation is vacuously satisfied.
                f.remove(head);
                changed = true;
                ++head;
                continue;
            }

            ++head; // no further progress possible this round: left pending.
        }
        if (head != f.qhead()) {
            f.advance_qhead(head);
            changed = true;
        }
        if (f.is_satisfied())
            return stx::simplify_result::satisfied;
        return changed ? stx::simplify_result::proceed : stx::simplify_result::noop;
    }

} // namespace seq
