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

    TODO: review and realize other ways to resolve remaining comparisons based on theory_seq.
--*/
#include "ast/seq/seq_lex_facet.h"
#include "ast/ast_pp.h"
#include <algorithm>
#include <functional>

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

    // A token list is only *guaranteed* to denote a non-empty sequence
    // when one of its tokens is a unit() (a single character is always
    // length 1). Any other token (an opaque variable/term) could still
    // be bound to the empty sequence, so its presence in the list does
    // not by itself establish non-emptiness.
    static bool contains_unit(seq_util& u, expr_ref_vector const& v) {
        for (expr* t : v)
            if (u.str.is_unit(t))
                return true;
        return false;
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
            // If it is strict, then R must contain a non-empty sequence
            // for lhs < rhs to hold; this is guaranteed only if R
            // contains a unit token. Otherwise leave the obligation
            // pending (a split rule elsewhere must first show one of
            // R's variables has length > 0).
            if (L.empty() && !R.empty()) {
                if (lx.m_strict && !contains_unit(u, R)) {
                    ++i;
                    continue;
                }
                // lhs is a proper prefix of rhs: lhs < rhs holds (both
                // strict and non-strict obligations are satisfied).
                remove(i);
                changed = true;
                continue;
            }
            // rhs is a proper prefix of lhs: lhs > rhs holds only if L is
            // guaranteed non-empty beyond rhs, i.e. is_strict, or L
            // contains a unit token (definitely non-empty). Otherwise
            // leave pending, since L could still collapse to equal rhs.
            if (!L.empty() && R.empty()) {
                if (!lx.m_strict && !contains_unit(u, L)) {
                    ++i;
                    continue;
                }
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
        bool cyc_conflict = false;
        eq_tree::dep_tracker cyc_dep = nullptr;
        bool cyc_changed = f.detect_cycles(cyc_conflict, cyc_dep, ac.eq_facet_ref());
        if (cyc_conflict) {
            n.set_conflict(stx::br_plugin_base, cyc_dep);
            return stx::simplify_result::conflict;
        }
        if (f.is_satisfied())
            return stx::simplify_result::satisfied;
        return (changed || cyc_changed) ? stx::simplify_result::proceed : stx::simplify_result::noop;
    }

    bool lex_facet::detect_cycles(bool& conflict, eq_tree::dep_tracker& conflict_dep, eq_facet& eqf) {
        conflict = false;
        conflict_dep = nullptr;

        // Collect the subset of pending obligations that have been
        // simplified down to a single variable/opaque term on each
        // side; these are the only ones we can place as edges into a
        // variable-level comparison graph. Everything else (still
        // multi-token) is left untouched.
        obj_map<expr, unsigned> var_id;
        ptr_vector<expr> vars;
        struct edge { unsigned src, dst; bool strict; unsigned lex_idx; };
        vector<edge> edges;

        auto get_id = [&](expr* v) {
            unsigned id;
            if (var_id.find(v, id))
                return id;
            id = vars.size();
            vars.push_back(v);
            var_id.insert(v, id);
            return id;
        };

        expr_ref_vector pin(m);
        for (unsigned i = 0; i < m_lexs.size(); ++i) {
            str_lex const& lx = m_lexs[i];
            if (lx.m_lhs.empty() && lx.m_rhs.empty())
                continue;
            sort* s = (lx.m_lhs.empty() ? lx.m_rhs.get(0) : lx.m_lhs.get(0))->get_sort();
            expr* l = u.str.mk_concat(lx.m_lhs, s);
            expr* r = u.str.mk_concat(lx.m_rhs, s);
            pin.push_back(l);
            pin.push_back(r);
            edges.push_back({ get_id(l), get_id(r), lx.m_strict, i });
        }
        if (edges.empty())
            return false;

        // Build adjacency and look for a cycle via DFS, tracking
        // whether any edge along the current path is strict.
        vector<vector<unsigned>> adj(vars.size());
        for (unsigned ei = 0; ei < edges.size(); ++ei)
            adj[edges[ei].src].push_back(ei);

        enum class color { white, gray, black };
        vector<color> colors(vars.size(), color::white);
        vector<unsigned> on_path;      // stack of edge indices on current DFS path
        vector<unsigned> path_node;    // stack of node ids on current DFS path

        std::function<bool(unsigned)> dfs = [&](unsigned u_id) -> bool {
            colors[u_id] = color::gray;
            path_node.push_back(u_id);
            for (unsigned ei : adj[u_id]) {
                unsigned v_id = edges[ei].dst;
                on_path.push_back(ei);
                if (colors[v_id] == color::gray) {
                    // Found a cycle: it consists of the edges on
                    // on_path from v_id's first occurrence onward.
                    unsigned start = 0;
                    while (path_node[start] != v_id) ++start;
                    bool has_strict = false;
                    eq_tree::dep_tracker dep = nullptr;
                    for (unsigned k = start; k < on_path.size(); ++k) {
                        edge const& e = edges[on_path[k]];
                        has_strict |= e.strict;
                        dep = m_dm.mk_join(dep, m_lexs[e.lex_idx].m_dep);
                    }
                    if (has_strict) {
                        conflict = true;
                        conflict_dep = dep;
                        return true;
                    }
                    // All-non-strict cycle: every variable on it is
                    // forced pairwise equal - re-assert as equations on
                    // eqf and drop these obligations from lex_facet
                    // (removing high indices first so lower indices
                    // stay valid).

v                   vector<unsigned> to_remove;
                    for (unsigned k = start; k < on_path.size(); ++k)
                        to_remove.push_back(edges[on_path[k]].lex_idx);
                    std::sort(to_remove.begin(), to_remove.end(), std::greater<unsigned>());
                    for (unsigned idx : to_remove) {
                        str_lex const& lx = m_lexs[idx];
                        eqf.add_equation(lx.m_lhs, lx.m_rhs, dep);
                        remove(idx);
                    }
                    return true;
                }
                if (colors[v_id] == color::white && dfs(v_id))
                    return true;
                on_path.pop_back();
            }
            path_node.pop_back();
            colors[u_id] = color::black;
            return false;
        };

        for (unsigned i = 0; i < vars.size(); ++i)
            if (colors[i] == color::white && dfs(i))
                return true;
        return false;
    }

} // namespace seq

