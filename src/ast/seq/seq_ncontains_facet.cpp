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
#include "ast/seq/seq_mem_facet.h"
#include "ast/seq/seq_solver_facet_i.h"
#include "ast/ast_pp.h"
#include "ast/rewriter/th_rewriter.h"
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
                // A substitution can invalidate an earlier "no further
                // progress" verdict, so rescan this obligation next round.
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

    uint64_t str_ncontains::hash() const {
        uint64_t h = stx::stx_hash_tag(0x6e636fu); // tag: "nco"
        h = stx::stx_hash_ids(h, m_haystack);
        h = stx::stx_hash_ids(h, m_needle);
        return h;
    }

    bool str_ncontains::equals(stx::constraint_i const& other) const {
        auto const* o = dynamic_cast<str_ncontains const*>(&other);
        return o && m_haystack == o->m_haystack && m_needle == o->m_needle;
    }

    void ncontains_facet::append_constraints(vector<stx::constraint_i const*>& out) const {
        for (auto const& nc : m_ncs)
            if (nc.active())
                out.push_back(&nc);
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
            if (!u.str.is_unit(ht) || !u.str.is_unit(nt))
                return l_undef; // unknown length: later tokens are not aligned
            if (m.are_distinct(ht, nt))
                return l_false; // distinct resolved constants: determined mismatch
            undef = true;
        }
        return undef ? l_undef : l_true;
    }

    static bool contains_tokens(expr_ref_vector const& haystack, expr_ref_vector const& needle) {
        if (needle.empty())
            return true;
        if (haystack.size() < needle.size())
            return false;
        for (unsigned i = 0; i + needle.size() <= haystack.size(); ++i) {
            bool match = true;
            for (unsigned j = 0; j < needle.size(); ++j)
                if (haystack.get(i + j) != needle.get(j)) {
                    match = false;
                    break;
                }
            if (match)
                return true;
        }
        return false;
    }

    // Every token of ts denotes a word in w*: constant runs, powers with a base
    // in w*, variables with a plain membership in a subset of w*. An empty w is
    // fixed by the first nonempty word seen.
    static bool tokens_in_word_star(seq_util& u, mem_facet const& mf, eq_tree::dep_manager_t& dm,
                                    expr_ref_vector const& ts, zstring& w, eq_tree::dep_tracker& dep) {
        zstring run, base;
        for (expr* t : ts) {
            expr* ch = nullptr, *b = nullptr, *k = nullptr;
            unsigned c = 0;
            if (u.str.is_unit(t, ch) && u.is_const_char(ch, c)) {
                run += zstring(c);
                continue;
            }
            if (u.str.is_power(t, b, k)) {
                if (!u.str.is_string(b, base) || !is_word_power(base, w))
                    return false;
            }
            else {
                bool found = false;
                for (str_mem const& sm : mf.memberships()) {
                    zstring w1 = w;
                    if (sm.active() && sm.is_plain() && sm.m_str.size() == 1 && sm.m_str.get(0) == t &&
                        is_in_word_star(u, sm.m_view.m_state, w1)) {
                        w = w1;
                        dep = dm.mk_join(dep, sm.m_dep);
                        found = true;
                        break;
                    }
                }
                if (!found)
                    return false;
            }
            if (!is_word_power(run, w))
                return false;
            run = zstring();
        }
        return is_word_power(run, w);
    }

    stx::simplify_result ncontains_propagation::propagate(eq_tree::node& n) {
        auto ac = get_ambient(n);
        auto& f = ac.ncontains_facet_ref();
        auto& ef = ac.eq_facet_ref();
        auto& sf = ac.solver_facet_ref();
        m_stats.m_num_propagate++;

        bool changed = false;
        // Try cheap model completion before revisiting obligations that word
        // equations deferred without a substitution touching them.
        if (ef.is_satisfied() && ac.assumption_facet_ref().model_completion_blocked()) {
            for (unsigned i = 0; i < f.qhead(); ++i) {
                auto const& nc = f.ncontains()[i];
                if (nc.active() && all_of(nc.m_needle, [&](expr* token) {
                        return u.str.is_unit(token) && m.is_value(token);
                    })) {
                    f.rewind_qhead(i);
                    break;
                }
            }
        }
        // Incremental scan over `[qhead, ncontains().size())`. Replacements
        // are appended past the current position and picked up later in the
        // same scan; `apply_subst` rewinds `qhead` when needed.
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

            // If an active equation exposes the forbidden needle as a
            // syntactic infix of this exact haystack, the negative
            // containment is already inconsistent. This also handles
            // guarded indexof decompositions whose self-referential
            // skolems prevent ordinary variable substitution.
            for (auto const& eq : ef.equations()) {
                if (!eq.active())
                    continue;
                bool conflict =
                    (eq.m_lhs == nc.m_haystack && contains_tokens(eq.m_rhs, nc.m_needle)) ||
                    (eq.m_rhs == nc.m_haystack && contains_tokens(eq.m_lhs, nc.m_needle));
                if (conflict) {
                    n.set_conflict(stx::br_plugin_base, f.dm().mk_join(nc.m_dep, eq.m_dep));
                    return stx::simplify_result::conflict;
                }
            }

            // Try every token-aligned starting position of the needle in the
            // current haystack.
            //   - some determined match => conflict;
            //   - every position a determined mismatch => discharge;
            //   - otherwise leave undecided positions pending, but strip any
            //     leading run of determined mismatches as safe progress.
            // If the haystack is currently shorter than the needle, leave
            // the obligation pending.
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
                    // A later position may still be a determined match.
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

            // Concrete needles admit a regular exclusion language.
            bool concrete_needle = all_of(nc.m_needle, [&](expr* token) {
                return u.str.is_unit(token) && m.is_value(token);
            });
            if (concrete_needle) {
                expr_ref literal(u.str.mk_concat(nc.m_needle, nc.m_needle[0]->get_sort()), m);
                // Reach targets use AST identity. Normalize String units before
                // symbolic and concrete derivatives can produce different states.
                th_rewriter rw(m);
                rw(literal);
                expr_ref all(u.re.mk_full_seq(u.re.mk_re(literal->get_sort())), m);
                expr_ref needle(u.re.mk_to_re(literal), m);
                expr_ref tail(u.re.mk_concat(needle, all), m);
                expr_ref containing(u.re.mk_concat(all, tail), m);
                expr_ref avoiding(u.re.mk_complement(containing), m);
                if (n_size == 1) {
                    // A single element cannot straddle concatenation boundaries.
                    expr* forbidden = to_app(nc.m_needle[0])->get_arg(0);
                    for (expr* token : nc.m_haystack) {
                        expr* character = nullptr;
                        if (u.str.is_unit(token, character)) {
                            if (!m.are_distinct(character, forbidden)) {
                                expr_ref different(m.mk_not(m.mk_eq(character, forbidden)), m);
                                ac.add_assumption(different, nc.m_dep);
                            }
                        }
                        else {
                            expr_ref_vector term(m);
                            term.push_back(token);
                            ac.mem_facet_ref().add(str_mem(m, term, view::membership(avoiding, m), nc.m_dep));
                        }
                    }
                }
                else
                    ac.mem_facet_ref().add(str_mem(m, nc.m_haystack, view::membership(avoiding, m), nc.m_dep));
                f.remove(head);
                changed = true;
                ++head;
                continue;
            }

            // Finite unit words require a mismatch in every possible alignment.
            // Bound the expansion before constructing its character formulas.
            if (!concrete_needle && has_window &&
                n_size <= 256u / (max_pos + 1) &&
                all_of(nc.m_haystack, [&](expr* token) { return u.str.is_unit(token); }) &&
                all_of(nc.m_needle, [&](expr* token) { return u.str.is_unit(token); })) {
                expr_ref_vector different(m);
                for (unsigned pos = 0; pos <= max_pos; ++pos) {
                    different.reset();
                    for (unsigned i = 0; i < n_size; ++i) {
                        expr* hch = nullptr;
                        expr* nch = nullptr;
                        VERIFY(u.str.is_unit(nc.m_haystack.get(pos + i), hch));
                        VERIFY(u.str.is_unit(nc.m_needle.get(i), nch));
                        if (hch != nch)
                            different.push_back(m.mk_not(m.mk_eq(hch, nch)));
                    }
                    expr_ref clause(m.mk_or(different.size(), different.data()), m);
                    if (auto false_dep = ac.literal_if_false(clause)) {
                        n.set_conflict(stx::br_plugin_base, f.dm().mk_join(nc.m_dep, false_dep));
                        return stx::simplify_result::conflict;
                    }
                    ac.add_assumption(clause, nc.m_dep);
                }
                f.remove(head);
                changed = true;
                ++head;
                continue;
            }

            // Units give a lower haystack bound and an exact all-unit needle length.
            if (all_of(nc.m_needle, [&](expr* token) {
                    expr* character = nullptr;
                    return u.str.is_unit(token, character);
                })) {
                unsigned lower = 0;
                for (expr* token : nc.m_haystack) {
                    expr* character = nullptr;
                    if (u.str.is_unit(token, character))
                        ++lower;
                }
                if (lower >= n_size) {
                    ++head;
                    continue;
                }
            }

            // Length gate: after the cheap token scan above, ask whether
            // `len(h) < len(n)` is already implied. Token counts are not a
            // sound proxy here because variable tokens may denote strings of
            // any length. Checked last because it calls the arithmetic
            // solver.
            expr* h_expr = tokens_to_expr(u, m, nc.m_haystack);
            expr* n_expr = tokens_to_expr(u, m, nc.m_needle);
            expr_ref len_h(u.str.mk_length(h_expr), m);
            expr_ref len_n(u.str.mk_length(n_expr), m);
            expr_ref gate(m.mk_not(a.mk_le(len_n, len_h)), m); // len(h) < len(n)

            // In w*, w^i contains w^j iff j <= i, i.e. iff len(n) <= len(h).
            zstring w;
            eq_tree::dep_tracker wdep = nc.m_dep;
            if (tokens_in_word_star(u, ac.mem_facet_ref(), f.dm(), nc.m_needle, w, wdep) &&
                tokens_in_word_star(u, ac.mem_facet_ref(), f.dm(), nc.m_haystack, w, wdep)) {
                ac.add_assumption(gate, wdep);
                f.remove(head);
                changed = true;
                ++head;
                continue;
            }

            if (sf.implies(gate) == l_true) {
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
        if (!changed)
            return stx::simplify_result::noop;
        return f.is_satisfied() ? stx::simplify_result::satisfied : stx::simplify_result::proceed;
    }

    void ncontains_split::apply_case(
        eq_tree::node& n, unsigned idx, expr* condition, bool shorter, eq_tree::edge& out) {
        auto ac = get_ambient(n);
        auto& sf = ac.solver_facet_ref();
        auto& a = sf.get_arith_util();
        auto& f = ac.ncontains_facet_ref();
        auto const& nc = f.ncontains()[idx];
        expr_ref zero(a.mk_int(0), m);
        for (auto const* tokens : { &nc.m_haystack, &nc.m_needle })
            for (expr* token : *tokens)
                if (!u.str.is_unit(token))
                    sf.add_constraint(a.mk_ge(u.str.mk_length(token), zero));
        auto dep = ac.assumption_facet_ref().add_assumption(condition, ac.context());
        sf.add_constraint(condition, dep);
        if (shorter)
            f.remove(idx);
        out = eq_tree::edge(shorter ? "ncontains len<" : "ncontains len>=", dep, true, 0);
    }

    scoped_ptr<eq_tree::split_iterator_i> ncontains_split::split(
        eq_tree::node& n, unsigned, eq_tree::edge& out, bool& has_more, bool& committed) {
        has_more = false;
        committed = false;
        auto ac = get_ambient(n);
        auto& f = ac.ncontains_facet_ref();
        if (f.is_satisfied())
            return nullptr;
        auto& sf = ac.solver_facet_ref();
        auto& a = sf.get_arith_util();
        th_rewriter rw(m);
        for (unsigned idx = 0; idx < f.ncontains().size(); ++idx) {
            auto const& nc = f.ncontains()[idx];
            if (!nc.active())
                continue;
            expr_ref haystack(tokens_to_expr(u, m, nc.m_haystack), m);
            expr_ref needle(tokens_to_expr(u, m, nc.m_needle), m);
            expr_ref len_h(u.str.mk_length(haystack), m);
            expr_ref len_n(u.str.mk_length(needle), m);
            expr_ref shorter(a.mk_lt(len_h, len_n), m);
            rw(shorter);
            expr_ref longer(m.mk_not(shorter), m);
            if (m.is_false(shorter) || sf.implies(longer) == l_true)
                continue;

            auto* it = alloc(iterator, n, *this, idx, longer, m);
            apply_case(n, idx, shorter, true, out);
            has_more = true;
            committed = true;
            ++m_num_splits;
            return it;
        }
        return nullptr;
    }

    bool ncontains_split::iterator::next(eq_tree::edge& out) {
        if (!m_pending)
            return false;
        m_pending = false;
        // A longer haystack may still avoid the needle: keep the obligation.
        m_owner.apply_case(m_n, m_idx, m_condition, false, out);
        return true;
    }

} // namespace seq
