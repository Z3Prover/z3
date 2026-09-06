/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_lex_facet.cpp

Abstract:

    See seq_lex_facet.h.

Author:

    Nikolaj Bjorner (nbjorner) 2026
    Clemens Eisenhofer 2026
    Margus Veanes 2026

Notes: 

    TODO: add cycle detection in the propagator as a separate step.
    Cycle detection builds a reachability graph based on asserted lt, le 
    constraints. There is a conflict if the graph contains a cycle with a strict edge.
    If the graph contains a cycle with non-strict edges, remove the involved comparisons
    and add them as equalities instead to the equality facet. Make sure that the dependencies
    for added equalities is the join of all equalities involved in the cycle.

    TODO: review and realize other ways to resolve remaining comparisons based on theory_seq.
--*/
#include "ast/seq/seq_lex_facet.h"
#include "ast/ast_pp.h"
#include <algorithm>

namespace seq {

    void lex_facet::set_sides(unsigned idx, expr_ref_vector const& lhs, expr_ref_vector const& rhs) {
        m_trail.push(vector_field_trail<str_lex, expr_ref_vector>(m_lexs, idx, &str_lex::m_lhs));
        m_trail.push(vector_field_trail<str_lex, expr_ref_vector>(m_lexs, idx, &str_lex::m_rhs));
        m_lexs[idx].m_lhs.reset();
        m_lexs[idx].m_lhs.append(lhs);
        m_lexs[idx].m_rhs.reset();
        m_lexs[idx].m_rhs.append(rhs);
    }

    void lex_facet::apply_subst(expr* var, expr_ref_vector const& repl, eq_tree::dep_tracker subst_dep) {
        for (unsigned i = 0; i < m_lexs.size(); ++i) {
            bool touched_l = subst_in_trailed(m_trail, m_lexs, i, &str_lex::m_lhs, var, repl);
            bool touched_r = subst_in_trailed(m_trail, m_lexs, i, &str_lex::m_rhs, var, repl);
            if ((touched_l || touched_r) && subst_dep) {
                m_trail.push(vector_field_trail<str_lex, eq_tree::dep_tracker>(m_lexs, i, &str_lex::m_dep));
                m_lexs[i].m_dep = m_dm.mk_join(m_lexs[i].m_dep, subst_dep);
            }
        }
    }

    stx::facet_i* lex_facet::clone(trail_stack& trail) const {
        lex_facet* f = alloc(lex_facet, trail, m, u, m_dm);
        f->m_lexs.append(m_lexs);
        return f;
    }

    std::ostream& lex_facet::display(std::ostream& out) const {
        out << "lex_facet: " << m_lexs.size() << " obligation(s)\n";
        for (auto const& lx : m_lexs) {
            out << "  [";
            for (expr* t : lx.m_lhs) out << mk_pp(t, m) << " ";
            out << "] " << (lx.m_strict ? "<" : "<=") << " [";
            for (expr* t : lx.m_rhs) out << mk_pp(t, m) << " ";
            out << "]\n";
        }
        return out;
    }

    // Compare two unit/character-constant tokens' underlying character
    // values; returns -1/0/1. Precondition: both are u.str.is_unit with a
    // u.is_const_char payload (checked by the caller).
    static int cmp_const_chars(seq_util& u, expr* a, expr* b) {
        expr* ca = nullptr, *cb = nullptr;
        VERIFY(u.str.is_unit(a, ca));
        VERIFY(u.str.is_unit(b, cb));
        unsigned na = 0, nb = 0;
        VERIFY(u.is_const_char(ca, na));
        VERIFY(u.is_const_char(cb, nb));
        return na < nb ? -1 : (na == nb ? 0 : 1);
    }

    static bool is_const_char_unit(seq_util& u, expr* tok) {
        expr* c = nullptr;
        return u.str.is_unit(tok, c) && u.is_const_char(c);
    }

    bool lex_facet::simplify(bool& conflict, eq_tree::dep_tracker& conflict_dep) {
        conflict = false;
        conflict_dep = nullptr;
        bool changed = false;
        for (unsigned i = 0; i < m_lexs.size(); ) {
            str_lex& lx = m_lexs[i];
            expr_ref_vector const& L0 = lx.m_lhs;
            expr_ref_vector const& R0 = lx.m_rhs;

            // Strip every leading pair of tokens already known equal
            // (same pointer, or two equal character constants) - always
            // sound regardless of m_strict.
            unsigned li = 0, ri = 0;
            while (li < L0.size() && ri < R0.size()) {
                expr* lh = L0.get(li);
                expr* rh = R0.get(ri);
                bool tok_eq = (lh == rh);
                if (!tok_eq && is_const_char_unit(u, lh) && is_const_char_unit(u, rh))
                    tok_eq = (cmp_const_chars(u, lh, rh) == 0);
                if (!tok_eq)
                    break;
                ++li; ++ri;
            }
            if (li > 0 || ri > 0) {
                expr_ref_vector newL(m), newR(m);
                newL.append(L0.size() - li, L0.data() + li);
                newR.append(R0.size() - ri, R0.data() + ri);
                set_sides(i, newL, newR);
                changed = true;
            }

            expr_ref_vector const& L = m_lexs[i].m_lhs;
            expr_ref_vector const& R = m_lexs[i].m_rhs;

            if (L.empty() && R.empty()) {
                // lhs == rhs: holds iff not strict.
                if (lx.m_strict) {
                    conflict = true;
                    conflict_dep = lx.m_dep;
                    return true;
                }
                remove(i);
                changed = true;
                continue;
            }
            // NSB code reivew: this is unsound for strict.
            // If it is strict, then R must contain a non-empty sequence
            // This is true if R contains a unit.
            // Otherwise it is a split rule to ensure one of the variables in R has length > 0.
            if (L.empty() && !R.empty()) {
                // lhs is a proper prefix of rhs: lhs < rhs holds (both
                // strict and non-strict obligations are satisfied).
                remove(i);
                changed = true;
                continue;
            }
            // NSB code review: this is only a conflict if L contains a non-empty
            // sequence, or if is_strict is true.
            if (!L.empty() && R.empty()) {
                // rhs is a proper prefix of lhs: lhs > rhs, so the
                // obligation (lhs < rhs, or lhs <= rhs) fails outright.
                conflict = true;
                conflict_dep = lx.m_dep;
                return true;
            }
            // Both nonempty, leading tokens neither pointer-equal nor
            // equal constants (else stripped above already).
            expr* lh = L.get(0);
            expr* rh = R.get(0);
            if (is_const_char_unit(u, lh) && is_const_char_unit(u, rh)) {
                // Distinct constants: the comparison is decided outright.
                int c = cmp_const_chars(u, lh, rh);
                SASSERT(c != 0); // equal case already stripped above
                if (c < 0) {
                    // lhs < rhs regardless of m_strict.
                    remove(i);
                    changed = true;
                    continue;
                }
                else {
                    // lhs > rhs: obligation fails.
                    conflict = true;
                    conflict_dep = lx.m_dep;
                    return true;
                }
            }            
            // Otherwise stuck (at least one leading token is a
            // variable/opaque term): leave pending for a future round,
            // e.g. once a substitution from eq_facet's split narrows it
            // further (see apply_subst above).
            ++i;
        }
        return changed;
    }

    stx::simplify_result lex_propagation::propagate(eq_tree::node& n) {
        auto ac = get_ambient(n);
        auto& f = ac.lex_facet_ref();
        bool conflict = false;
        eq_tree::dep_tracker conflict_dep = nullptr;
        m_stats.m_num_propagate++;
        bool changed = f.simplify(conflict, conflict_dep);
        if (conflict) {
            n.set_conflict(stx::br_plugin_base, conflict_dep);
            return stx::simplify_result::conflict;
        }
        if (f.is_satisfied())
            return stx::simplify_result::satisfied;
        return changed ? stx::simplify_result::proceed : stx::simplify_result::noop;
    }

} // namespace seq
