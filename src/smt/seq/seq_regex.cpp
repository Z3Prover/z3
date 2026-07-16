/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_regex.cpp

Abstract:

    Lazy regex membership processing for the Nielsen-based string solver.

Author:

    Clemens Eisenhofer 2026-03-01
    Nikolaj Bjorner (nbjorner) 2026-03-01

--*/
#include "smt/seq/seq_regex.h"
#include "ast/rewriter/seq_range_collapse.h"

namespace seq {

    // Collect possible first characters of a syntactically known *string*
    // expression (the body of to_re). Regex operators (union, complement,
    // intersection, ...) are not expected here.
    void collect_possible_first_chars(seq_util& seq, euf::sgraph const& sg, expr* str,
                                      unsigned_vector& bounds, bool& may_be_empty) {
        may_be_empty = false;
        SASSERT(str);
        sort* re_sort = nullptr;
        VERIFY(!seq.is_re(str, re_sort));

        unsigned ch = 0;
        if (sg.decode_re_char(str, ch)) {
            bounds.push_back(ch);
            if (ch < zstring::max_char())
                bounds.push_back(ch + 1);
            return;
        }

        zstring s;
        if (seq.str.is_string(str, s)) {
            if (s.length() == 0) {
                may_be_empty = true;
                return;
            }
            unsigned first_ch = s[0];
            bounds.push_back(first_ch);
            if (first_ch < zstring::max_char())
                bounds.push_back(first_ch + 1);
            return;
        }

        expr* a = nullptr;
        expr* b = nullptr;
        if (seq.str.is_concat(str, a, b)) {
            bool a_may_be_empty = false;
            collect_possible_first_chars(seq, sg, a, bounds, a_may_be_empty);

            if (a_may_be_empty) {
                bool b_may_be_empty = false;
                collect_possible_first_chars(seq, sg, b, bounds, b_may_be_empty);
                may_be_empty = b_may_be_empty;
            }
            return;
        }
        std::cout << "Unexpected: " << mk_pp(str, sg.get_manager()) << std::endl;

        UNREACHABLE();
    }


    // -----------------------------------------------------------------------
    // Uniform derivative (symbolic character consumption)
    // -----------------------------------------------------------------------

    euf::snode const* seq_regex::try_uniform_derivative(euf::snode const* regex) const {
        if (!regex)
            return nullptr;

        // Quick exits: trivial regexes with known uniform derivatives.
        // Σ* (full_seq) has derivative Σ* for every character.
        if (regex->is_full_seq())
            return regex;
        // ∅ (fail) has derivative ∅ for every character — but this means
        // every character is rejected.  Return fail so the caller can
        // detect a conflict.
        if (regex->is_fail())
            return regex;

        // Compute minterms: the character-class partition of the alphabet
        // induced by the regex.
        euf::snode_vector minterms;
        m_sg.compute_minterms(regex, minterms);
        if (minterms.empty())
            return nullptr;

        // Compute the derivative for each non-empty minterm.  If all produce
        // the same result, the derivative is independent of the character
        // value and we can consume a symbolic character deterministically.
        euf::snode const* uniform = nullptr;
        for (euf::snode const* mt : minterms) {
            if (!mt || mt->is_fail())
                continue;  // empty character class — no character belongs to it
            euf::snode const* deriv = m_sg.brzozowski_deriv(regex, mt);
            if (!deriv)
                return nullptr;  // derivative computation failed
            if (!uniform) {
                uniform = deriv;
            } else if (uniform->id() != deriv->id()) {
                return nullptr;  // different derivatives — not uniform
            }
        }
        return uniform;  // may be nullptr if all minterms were fail/empty
    }

    // -----------------------------------------------------------------------
    // Basic regex predicates
    // -----------------------------------------------------------------------

    bool seq_regex::is_empty_regex(euf::snode const* re) const {
        SASSERT(re);
        // direct empty language constant
        if (re->is_fail())
            return true;
        // kinds that are never empty
        if (re->is_star() || re->is_to_re() || re->is_range() ||
            re->is_full_char() || re->is_full_seq())
            return false;
        // loop with lo == 0 accepts ε
        if (re->is_loop() && is_nullable(re))
            return false;

        expr* e = re->get_expr();

        expr* r1, * r2;
        // union is empty iff both children are empty
        if (seq.re.is_union(e, r1, r2)) {
            SASSERT(re->num_args() == 2);
            return is_empty_regex(re->arg(0)) && is_empty_regex(re->arg(1));
        }
        // regex concat is empty if either child is empty
        if (seq.re.is_concat(e, r1, r2)) {
            SASSERT(re->num_args() == 2);
            return is_empty_regex(re->arg(0)) || is_empty_regex(re->arg(1));
        }
        // intersection is empty if either child is empty
        if (seq.re.is_intersection(e, r1, r2)) {
            SASSERT(re->num_args() == 2);
            if (is_empty_regex(re->arg(0)) || is_empty_regex(re->arg(1)))
                return true;
        }
        // complement of full_seq is empty
        if (re->is_complement() && re->num_args() == 1 && re->arg(0)->is_full_seq())
            return true;
        // loop(empty, lo, _) with lo > 0 is empty
        if (re->is_loop() && re->num_args() >= 1 && is_empty_regex(re->arg(0)))
            return !is_nullable(re); // empty if not nullable (i.e., lo > 0)

        return false;
    }

    // -----------------------------------------------------------------------
    // BFS regex emptiness check — helper: collect character boundaries
    // This is faster than computing the actual minterms but probably not minimal
    // -----------------------------------------------------------------------
    void seq_regex::collect_char_boundaries(euf::snode const* re, unsigned_vector& bounds) const {
        SASSERT(re && re->get_expr());

        expr* e = re->get_expr();

        // Range predicate re.range(lo, hi): boundary at lo and hi+1
        // Range arguments are string expressions (e.g., str.unit(ch))
        expr* lo_expr = nullptr;
        expr* hi_expr = nullptr;
        if (seq.re.is_range(e, lo_expr, hi_expr)) {
            unsigned lo = 0, hi = 0;
            if (m_sg.decode_re_char(lo_expr, lo))
                bounds.push_back(lo);
            if (m_sg.decode_re_char(hi_expr, hi) && hi < zstring::max_char())
                bounds.push_back(hi + 1);
            return;
        }

        // to_re(s): boundary at possible first characters of s
        expr* body = nullptr;
        if (seq.re.is_to_re(e, body)) {
            bool may_be_empty = false;
            collect_possible_first_chars(seq, m_sg, body, bounds, may_be_empty);
            return;
        }

        // Leaf nodes with no character discrimination
        if (re->is_fail() || re->is_full_char() || re->is_full_seq())
            return;

        // re.of_pred over a range-fragment lambda: the canonical multi-range
        // character class (see seq::range_predicate_to_regex).  Boundaries at
        // every interval edge.  Outside the fragment the snode is non-ground
        // (see sgraph::compute_metadata) and is_empty_bfs's ground gate keeps
        // it away from this partition.
        if (seq.re.is_of_pred(e)) {
            range_predicate rp(seq.max_char());
            if (regex_to_range_predicate(seq, e, rp)) {
                for (unsigned i = 0; i < rp.num_ranges(); ++i) {
                    auto [rlo, rhi] = rp[i];
                    bounds.push_back(rlo);
                    if (rhi < zstring::max_char())
                        bounds.push_back(rhi + 1);
                }
            }
            return;
        }

        // If we reached a leaf and none of the expected leaf forms matched,
        // this is a regex constructor we did not account for in boundary
        // extraction and should fail loudly in debug builds.
        if (re->num_args() == 0) {
            UNREACHABLE();
            return;
        }

        // Recurse into children (handles union, concat, star, loop, etc.)
        for (unsigned i = 0; i < re->num_args(); ++i) {
            collect_char_boundaries(re->arg(i), bounds);
        }
    }

    // -----------------------------------------------------------------------
    // BFS regex emptiness check — helper: alphabet representatives
    // Faster alternative of computing all min-terms and taking representatives of them
    // -----------------------------------------------------------------------
    bool seq_regex::get_alphabet_representatives(euf::snode const* re, euf::snode_vector& reps) {
        if (!re || !re->get_expr())
            return false;

        unsigned max_c = seq.max_char();

        // Partition the alphabet using boundary points induced by regex
        // predicates; one representative per interval is sufficient.
        unsigned_vector bounds;
        bounds.push_back(0);
        if (max_c < UINT_MAX)
            bounds.push_back(max_c + 1);
        collect_char_boundaries(re, bounds);

        std::sort(bounds.begin(), bounds.end());
        unsigned_vector uniq;
        for (unsigned b : bounds) {
            if (uniq.empty() || uniq.back() != b)
                uniq.push_back(b);
        }
        bounds = uniq;

        for (unsigned i = 0; i + 1 < bounds.size(); ++i) {
            unsigned lo = bounds[i];
            unsigned hi = bounds[i + 1];
            if (lo <= max_c && lo < hi)
                reps.push_back(m_sg.mk_char(lo));
        }

        // Defensive fallback for degenerate inputs.
        if (reps.empty())
            reps.push_back(m_sg.mk_char(0));
        return true;
    }

    // -----------------------------------------------------------------------
    // BFS regex emptiness check
    // -----------------------------------------------------------------------

    // NSB review: we have similar functionality in seq_rewriter::some_seq_in_re
    // currently both these versions only relly work for strings not general sequences
    lbool seq_regex::is_empty_bfs(euf::snode const* re, unsigned max_states) {
        SASSERT(re);
        const expr* e = re->get_expr();
        SASSERT(e);

        lbool cached_result;
        if (m_empty_cache.find(e->get_id(), cached_result))
            return cached_result;

        auto cache_and_return = [&](lbool result) {
            m_empty_cache.insert(e->get_id(), result);
            return result;
        };

        if (re->is_fail())
            return cache_and_return(l_true);
        if (is_nullable(re))
            return cache_and_return(l_false);
        // Structural quick checks for kinds that are never empty
        if (re->is_star() || re->is_full_char() || re->is_full_seq() || re->is_to_re() || re->is_range())
            return cache_and_return(l_false);
        // Structural emptiness catches simple cases
        if (is_empty_regex(re))
            return cache_and_return(l_true);
        // Only handle ground regexes; non-ground can't be fully explored
        if (!re->is_ground())
            return cache_and_return(l_undef);
        // s_var snodes (unrecognized regex kinds, e.g. re.+) cannot be
        // efficiently explored: the alphabet partition is trivially {∅} and
        // derivative computations may be slow.  Report l_undef and let the
        // caller fall back to a more capable procedure.
        if (re->is_var())
            return cache_and_return(l_undef);

        // BFS over the Brzozowski derivative automaton.
        // Each state is a derivative regex snode identified by its id.
        // We explore states by computing derivatives for representative
        // characters from the alphabet partition.
        uint_set visited;
        euf::snode_vector worklist;
        worklist.push_back(re);
        visited.insert(re->id());

        unsigned states_explored = 0;

        while (!worklist.empty()) {
            if (!m.inc())
                return l_undef; // don't cache
            if (states_explored >= max_states)
                return l_undef; // also don't cache

            euf::snode const* current = worklist.back();
            worklist.pop_back();
            ++states_explored;

            // Compute representative characters for current state's
            // alphabet partition. Each representative is a concrete
            // character snode whose equivalence class has identical
            // derivative behavior.
            euf::snode_vector reps;
            if (!get_alphabet_representatives(current, reps))
                return cache_and_return(l_undef);

            if (reps.empty())
                // Nothing found = dead-end
                continue;

            for (euf::snode const* ch : reps) {
                if (!m.inc())
                    return l_undef; // don't cache
                // std::cout << "Deriving by " << snode_label_html(ch, sg().get_manager()) << std::endl;
                euf::snode const* deriv = m_sg.brzozowski_deriv(current, ch);
                SASSERT(deriv);
                if (is_nullable(deriv))
                    return cache_and_return(l_false); // found an accepting state
                if (deriv->is_fail())
                    continue; // dead-end, no need to explore further
                if (is_empty_regex(deriv))
                    continue; // structurally empty subtree
                if (!visited.contains(deriv->id())) {
                    visited.insert(deriv->id());
                    worklist.push_back(deriv);
                }
            }
        }
        return cache_and_return(l_true);
    }

    // -----------------------------------------------------------------------
    // Multi-regex intersection emptiness check
    // BFS over the product of Brzozowski derivative automata.
    // -----------------------------------------------------------------------

    lbool seq_regex::check_intersection_emptiness(euf::snode_vector const& regexes, unsigned max_states) {

        if (regexes.empty())
            return l_false; // empty intersection = full language (vacuously non-empty)

        // Single regex: delegate to is_empty_bfs
        if (regexes.size() == 1)
            return is_empty_bfs(regexes[0], max_states);

        euf::snode const* result = regexes[0];
        for (unsigned i = 1; i < regexes.size(); ++i) {
            expr* r1 = result->get_expr();
            expr* r2 = regexes[i]->get_expr();
            SASSERT(r1 && r2);
            result = m_sg.mk(seq.re.mk_inter(r1, r2));
            SASSERT(result);
        }

        return is_empty_bfs(result, max_states);
    }

    // -----------------------------------------------------------------------
    // Ground prefix consumption
    // -----------------------------------------------------------------------

    seq_regex::simplify_status seq_regex::simplify_ground_prefix(seq::str_mem& mem) {
        if (!mem.m_str || !mem.m_regex)
            return simplify_status::ok;

        while (mem.m_str && !mem.m_str->is_empty()) {
            euf::snode const* first = mem.m_str->first();
            if (!first || !first->is_char())
                break;
            euf::snode const* parent_re = mem.m_regex;
            euf::snode const* deriv = m_sg.brzozowski_deriv(parent_re, first);
            if (!deriv)
                break;
            if (deriv->is_fail())
                return simplify_status::conflict;
            mem.m_str = m_sg.drop_first(mem.m_str);
            mem.m_regex = deriv;
        }

        // check final state
        if (mem.m_str && mem.m_str->is_empty()) {
            if (is_nullable(mem.m_regex))
                return simplify_status::satisfied;
            return simplify_status::conflict;
        }

        return simplify_status::ok;
    }

    // -----------------------------------------------------------------------
    // Ground suffix consumption (best-effort)
    // -----------------------------------------------------------------------

    seq_regex::simplify_status seq_regex::simplify_ground_suffix(seq::str_mem& mem) {
        // Suffix consumption via reverse derivatives is complex.
        // For now, only handle the case where the entire string is ground:
        // consume all characters from the front (which covers trailing chars
        // when the string is fully ground).
        if (!mem.m_str->is_ground())
            return simplify_status::ok;

        // If the string is ground, simplify_ground_prefix handles everything.
        return simplify_ground_prefix(mem);
    }

    // -----------------------------------------------------------------------
    // Trivial checks
    // -----------------------------------------------------------------------

    int seq_regex::check_trivial(seq::str_mem const& mem) const {
        SASSERT(mem.m_str && mem.m_regex);
        // regex is ∅ => always conflict
        if (is_empty_regex(mem.m_regex))
            return -1;
        // regex is Σ* => always satisfied
        if (is_full_regex(mem.m_regex))
            return 1;
        // empty string checks
        if (mem.m_str->is_empty()) {
            if (is_nullable(mem.m_regex))
                return 1;
            return -1;
        }
        return 0;
    }

    // -----------------------------------------------------------------------
    // Minterm computation with filtering
    // -----------------------------------------------------------------------

    void seq_regex::get_minterms(euf::snode const* regex, euf::snode_vector& minterms) {
        if (!regex)
            return;

        // compute raw minterms from the regex predicates
        euf::snode_vector raw;
        m_sg.compute_minterms(regex, raw);

        // filter: keep only minterms that are non-fail (non-empty character class).
        // note: minterms are regex character-class expressions, not concrete
        // characters, so we cannot compute Brzozowski derivatives with them.
        // callers should compute derivatives using concrete or fresh chars.
        for (euf::snode const* mt : raw) {
            if (!mt || mt->is_fail())
                continue;
            minterms.push_back(mt);
        }
    }

    // -----------------------------------------------------------------------
    // Membership processing
    // -----------------------------------------------------------------------

    bool seq_regex::process_str_mem(str_mem const& mem,
                                     vector<str_mem>& out_mems) {
        SASSERT(mem.m_str && mem.m_regex);
        // empty string: check nullable
        if (mem.m_str->is_empty())
            return is_nullable(mem.m_regex);

        // consume ground prefix: derive regex by each leading concrete char
        str_mem working = mem;
        const simplify_status st = simplify_ground_prefix(working);
        if (st == simplify_status::conflict)
            return false;
        if (st == simplify_status::satisfied)
            return true;

        // after ground prefix consumption, if the front is still a concrete
        // character we can take one more step (shouldn't happen after
        // simplify_ground_prefix, but guard defensively)
        euf::snode const* first = working.m_str->first();
        if (first && first->is_char()) {
            const str_mem derived = derive(working, first);
            if (is_empty_regex(derived.m_regex))
                return false;
            out_mems.push_back(derived);
            return true;
        }

        // string starts with a non-ground element (variable or unit):
        // return the simplified constraint for the Nielsen graph to expand
        // via character-split modifiers.
        out_mems.push_back(working);
        return true;
    }

    char_set seq_regex::minterm_to_char_set(expr* re_expr) {
        unsigned max_c = seq.max_char();

        if (!re_expr)
            return char_set::full(max_c);

        // full_char: the whole alphabet [0, max_char]
        if (seq.re.is_full_char(re_expr))
            return char_set::full(max_c);

        // range [lo, hi] (hi inclusive in Z3's regex representation)
        expr* lo_expr = nullptr;
        expr* hi_expr = nullptr;
        if (seq.re.is_range(re_expr, lo_expr, hi_expr)) {
            unsigned lo = 0, hi = 0;
            bool has_lo = false, has_hi = false;

            if (lo_expr) {
                if (m_sg.decode_re_char(lo_expr, lo)) {
                    has_lo = true;
                }
            }
            if (hi_expr) {
                if (m_sg.decode_re_char(hi_expr, hi)) {
                    has_hi = true;
                }
            }

            if (has_lo && has_hi) {
                SASSERT(lo <= hi);
                if (lo > hi)
                    return char_set();
                // char_range uses exclusive upper bound; Z3 hi is inclusive
                return char_set(char_range(lo, hi + 1));
            }
        }

        // complement: alphabet minus the inner set
        expr* inner = nullptr;
        if (seq.re.is_complement(re_expr, inner))
            return minterm_to_char_set(inner).complement(max_c);

        // union: characters present in either set
        expr* r1 = nullptr, *r2 = nullptr;
        if (seq.re.is_union(re_expr, r1, r2)) {
            char_set cs = minterm_to_char_set(r1);
            cs.add(minterm_to_char_set(r2));
            return cs;
        }

        // intersection: characters present in both sets
        if (seq.re.is_intersection(re_expr, r1, r2))
            return minterm_to_char_set(r1).intersect_with(minterm_to_char_set(r2));

        // difference: r1 minus r2 = r1 ∩ complement(r2)
        if (seq.re.is_diff(re_expr, r1, r2))
            return minterm_to_char_set(r1).intersect_with(
                       minterm_to_char_set(r2).complement(max_c));

        // to_re(str.unit(c)): singleton character set
        expr* str_arg = nullptr;
        unsigned char_val = 0;
        if (seq.re.is_to_re(re_expr, str_arg) && m_sg.decode_re_char(str_arg, char_val)) {
            char_set cs;
            cs.add(char_val);
            return cs;
        }

        // empty regex: no characters can appear
        if (seq.re.is_empty(re_expr))
            return char_set();

        // Unexpected minterm shape: we should fail loudly instead of silently
        // returning a conservative approximation.
        UNREACHABLE();
        return char_set::full(max_c);
    }

}