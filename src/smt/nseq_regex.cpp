/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    nseq_regex.cpp

Abstract:

    Lazy regex membership processing for the Nielsen-based string solver.

Author:

    Nikolaj Bjorner (nbjorner) 2026-03-01

--*/
#include "smt/nseq_regex.h"

namespace smt {

    // -----------------------------------------------------------------------
    // Regex emptiness checking (structural analysis)
    // -----------------------------------------------------------------------

    bool nseq_regex::is_empty_regex(euf::snode* re) const {
        if (!re)
            return false;
        // direct empty language constant
        if (re->is_fail())
            return true;
        // kinds that are never empty
        if (re->is_star() || re->is_to_re() ||
            re->is_full_char() || re->is_full_seq())
            return false;
        // loop with lo == 0 accepts ε
        if (re->is_loop() && re->is_nullable())
            return false;

        seq_util& seq = m_sg.get_seq_util();
        expr* e = re->get_expr();
        if (!e)
            return false;

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
            return !re->is_nullable(); // empty if not nullable (i.e., lo > 0)

        return false;
    }

    // -----------------------------------------------------------------------
    // Cycle detection
    // -----------------------------------------------------------------------

    bool nseq_regex::detect_cycle(seq::str_mem const& mem) const {
        return extract_cycle(mem) != nullptr;
    }

    // -----------------------------------------------------------------------
    // Ground prefix consumption
    // -----------------------------------------------------------------------

    nseq_regex::simplify_status nseq_regex::simplify_ground_prefix(seq::str_mem& mem) {
        if (!mem.m_str || !mem.m_regex)
            return simplify_status::ok;

        while (mem.m_str && !mem.m_str->is_empty()) {
            euf::snode* first = mem.m_str->first();
            if (!first || !first->is_char())
                break;
            euf::snode* deriv = m_sg.brzozowski_deriv(mem.m_regex, first);
            if (!deriv)
                break;
            if (deriv->is_fail())
                return simplify_status::conflict;
            mem.m_str = m_sg.drop_first(mem.m_str);
            mem.m_regex = deriv;
        }

        // check final state
        if (mem.m_str && mem.m_str->is_empty()) {
            if (mem.m_regex->is_nullable())
                return simplify_status::satisfied;
            return simplify_status::conflict;
        }

        return simplify_status::ok;
    }

    // -----------------------------------------------------------------------
    // Ground suffix consumption (best-effort)
    // -----------------------------------------------------------------------

    nseq_regex::simplify_status nseq_regex::simplify_ground_suffix(seq::str_mem& mem) {
        // Suffix consumption via reverse derivatives is complex.
        // For now, only handle the case where the entire string is ground:
        // consume all characters from the front (which covers trailing chars
        // when the string is fully ground).
        if (!mem.m_str || !mem.m_regex)
            return simplify_status::ok;
        if (!mem.m_str->is_ground())
            return simplify_status::ok;

        // If the string is ground, simplify_ground_prefix handles everything.
        return simplify_ground_prefix(mem);
    }

    // -----------------------------------------------------------------------
    // Trivial checks
    // -----------------------------------------------------------------------

    int nseq_regex::check_trivial(seq::str_mem const& mem) const {
        if (!mem.m_str || !mem.m_regex)
            return 0;
        // regex is ∅ => always conflict
        if (is_empty_regex(mem.m_regex))
            return -1;
        // regex is Σ* => always satisfied
        if (is_full_regex(mem.m_regex))
            return 1;
        // empty string checks
        if (mem.m_str->is_empty()) {
            if (mem.m_regex->is_nullable())
                return 1;
            return -1;
        }
        return 0;
    }

    // -----------------------------------------------------------------------
    // Minterm computation with filtering
    // -----------------------------------------------------------------------

    void nseq_regex::get_minterms(euf::snode* regex, euf::snode_vector& minterms) {
        if (!regex)
            return;

        // compute raw minterms from the regex predicates
        euf::snode_vector raw;
        m_sg.compute_minterms(regex, raw);

        // filter: keep only minterms that are non-fail (non-empty character class).
        // note: minterms are regex character-class expressions, not concrete
        // characters, so we cannot compute Brzozowski derivatives with them.
        // callers should compute derivatives using concrete or fresh chars.
        for (euf::snode* mt : raw) {
            if (!mt || mt->is_fail())
                continue;
            minterms.push_back(mt);
        }
    }

    // -----------------------------------------------------------------------
    // Collect first characters
    // -----------------------------------------------------------------------

    void nseq_regex::collect_first_chars(euf::snode* re, euf::snode_vector& chars) {
        if (!re)
            return;

        // to_re(s): extract first character of the string body
        if (re->is_to_re()) {
            euf::snode* body = re->arg(0);
            if (body && !body->is_empty()) {
                euf::snode* first = body->first();
                if (first && first->is_char()) {
                    bool dup = false;
                    for (euf::snode* c : chars)
                        if (c == first) { dup = true; break; }
                    if (!dup)
                        chars.push_back(first);
                }
                // Handle string literals (classified as s_other in sgraph)
                else if (first && first->get_expr()) {
                    seq_util& seq = m_sg.get_seq_util();
                    zstring s;
                    if (seq.str.is_string(first->get_expr(), s) && s.length() > 0) {
                        euf::snode* ch = m_sg.mk_char(s[0]);
                        bool dup = false;
                        for (euf::snode* c : chars)
                            if (c == ch) { dup = true; break; }
                        if (!dup)
                            chars.push_back(ch);
                    }
                }
            }
            return;
        }

        // leaf cases: produce representative characters for character classes
        if (re->is_full_char()) {
            // full character set (.): use 'a' as representative
            euf::snode* ch = m_sg.mk_char('a');
            bool dup = false;
            for (euf::snode* c : chars)
                if (c == ch) { dup = true; break; }
            if (!dup)
                chars.push_back(ch);
            return;
        }

        // re.range(lo, hi): use lo as representative
        if (re->get_expr()) {
            seq_util& seq = m_sg.get_seq_util();
            expr* lo = nullptr, *hi = nullptr;
            if (seq.re.is_range(re->get_expr(), lo, hi) && lo) {
                zstring s;
                unsigned ch_val = 'a';
                if (seq.is_const_char(lo, ch_val)) {
                    euf::snode* ch = m_sg.mk_char(ch_val);
                    bool dup = false;
                    for (euf::snode* c : chars)
                        if (c == ch) { dup = true; break; }
                    if (!dup)
                        chars.push_back(ch);
                }
                return;
            }
        }

        if (re->is_fail() || re->is_full_seq())
            return;

        // recurse into children (handles union, concat, star, loop, etc.)
        for (unsigned i = 0; i < re->num_args(); ++i)
            collect_first_chars(re->arg(i), chars);
    }

    // -----------------------------------------------------------------------
    // Membership processing
    // -----------------------------------------------------------------------

    bool nseq_regex::process_str_mem(seq::str_mem const& mem,
                                     vector<seq::str_mem>& out_mems) {
        if (!mem.m_str || !mem.m_regex)
            return true;
        // empty string: check nullable
        if (mem.m_str->is_empty())
            return mem.m_regex->is_nullable();

        // consume ground prefix: derive regex by each leading concrete char
        seq::str_mem working = mem;
        simplify_status st = simplify_ground_prefix(working);
        if (st == simplify_status::conflict)
            return false;
        if (st == simplify_status::satisfied)
            return true;

        // after ground prefix consumption, if the front is still a concrete
        // character we can take one more step (shouldn't happen after
        // simplify_ground_prefix, but guard defensively)
        euf::snode* first = working.m_str->first();
        if (first && first->is_char()) {
            seq::str_mem derived = derive(working, first);
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

    // -----------------------------------------------------------------------
    // History recording
    // -----------------------------------------------------------------------

    seq::str_mem nseq_regex::record_history(seq::str_mem const& mem, euf::snode* history_re) {
        // Build a history chain by prepending the new regex entry to the
        // existing history. Uses regex-concat as a cons cell:
        //   new_history = re.concat(history_re, old_history)
        // where arg(0) is the latest entry and arg(1) is the tail.
        // If old_history is nullptr, the new entry becomes the terminal leaf.
        euf::snode* new_history = history_re;
        if (mem.m_history && history_re) {
            expr* re_expr = history_re->get_expr();
            expr* old_expr = mem.m_history->get_expr();
            if (re_expr && old_expr) {
                seq_util& seq = m_sg.get_seq_util();
                expr_ref chain(seq.re.mk_concat(re_expr, old_expr), m_sg.get_manager());
                new_history = m_sg.mk(chain);
            }
        }
        return seq::str_mem(mem.m_str, mem.m_regex, new_history, mem.m_id, mem.m_dep);
    }

    // -----------------------------------------------------------------------
    // Cycle detection
    // -----------------------------------------------------------------------

    euf::snode* nseq_regex::extract_cycle(seq::str_mem const& mem) const {
        // Walk the history chain looking for a repeated regex.
        // A cycle exists when the current regex matches a regex in the history.
        if (!mem.m_regex || !mem.m_history)
            return nullptr;

        euf::snode* current = mem.m_regex;
        euf::snode* hist = mem.m_history;

        // Walk the history chain up to a bounded depth.
        // The history is structured as a chain of regex snapshots connected
        // via the sgraph's regex-concat: each level's arg(0) is a snapshot
        // and arg(1) is the tail. A leaf (non-concat) is a terminal entry.
        unsigned bound = 1000;
        while (hist && bound-- > 0) {
            euf::snode* entry = hist;
            euf::snode* tail = nullptr;

            // If the history node is a regex concat, decompose it:
            // arg(0) is the regex snapshot, arg(1) is the rest of the chain
            seq_util& seq = m_sg.get_seq_util();
            if (hist->is_concat() && hist->get_expr() &&
                seq.re.is_concat(hist->get_expr())) {
                entry = hist->arg(0);
                tail = hist->arg(1);
            }

            // Check pointer equality (fast, covers normalized regexes)
            if (entry == current)
                return entry;
            // Check expression-level equality as fallback
            if (entry->get_expr() && current->get_expr() &&
                entry->get_expr() == current->get_expr())
                return entry;

            hist = tail;
        }
        return nullptr;
    }

    // -----------------------------------------------------------------------
    // Stabilizer from cycle
    // -----------------------------------------------------------------------

    euf::snode* nseq_regex::stabilizer_from_cycle(euf::snode* cycle_regex,
                                                   euf::snode* current_regex) {
        if (!cycle_regex || !current_regex)
            return nullptr;

        // The stabilizer is the Kleene star of the "cycle body" regex.
        // If the cycle regex and current regex are the same (pointer equal),
        // the stabilizer is cycle_regex* (Kleene star).
        // This mirrors ZIPT's StabilizerFromCycle which extracts the
        // regex between the cycle entry and current point and wraps it in *.

        // Build cycle_regex* via the sgraph's expression factory
        expr* re_expr = cycle_regex->get_expr();
        if (!re_expr)
            return nullptr;

        seq_util& seq = m_sg.get_seq_util();
        expr_ref star_expr(seq.re.mk_star(re_expr), m_sg.get_manager());
        return m_sg.mk(star_expr);
    }

    // -----------------------------------------------------------------------
    // Stabilizer-based subsumption
    // -----------------------------------------------------------------------

    bool nseq_regex::try_subsume(seq::str_mem const& mem) {
        // Check if the derivation history exhibits a cycle, and if so,
        // whether the current regex is subsumed by the stabilizer.
        euf::snode* cycle = extract_cycle(mem);
        if (!cycle)
            return false;

        euf::snode* stab = stabilizer_from_cycle(cycle, mem.m_regex);
        if (!stab)
            return false;

        // A constraint x ∈ R is subsumed when R ⊆ stab.
        // For the simple case where cycle == current regex,
        // R ⊆ R* is always true (since R* accepts everything R does, and more).
        // This handles the common idempotent cycle case.
        if (cycle == mem.m_regex)
            return true;

        // More sophisticated subsumption checks (regex containment)
        // would require a regex inclusion decision procedure.
        // For now, only handle the pointer-equality case.
        return false;
    }

}
