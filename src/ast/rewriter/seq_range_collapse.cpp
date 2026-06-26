/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_range_collapse.cpp

Abstract:

    Implementation of regex <-> range_predicate translation for the
    boolean-combination-of-ranges fragment. See header for the recognized
    grammar and the canonical regex AST emitted by materialization.

Authors:

    Margus Veanes (veanes) 2026

--*/

#include "ast/rewriter/seq_range_collapse.h"

namespace seq {

    bool regex_to_range_predicate(seq_util& u, expr* r, range_predicate& out) {
        // The range algebra only models sets of single characters over the
        // unsigned character domain [0, max_char].  Guard against any regex
        // whose element type is not a sequence of characters (e.g. a regex
        // over (Seq Int) or (Seq (Seq Char))): for such regexes the
        // re.range/re.union/... matchers below would silently fabricate a
        // character-class predicate and change semantics.  Reject them up
        // front so callers fall back to the generic regex path.
        sort* seq_sort = nullptr;
        if (!u.is_re(r, seq_sort) || !u.is_string(seq_sort))
            return false;

        unsigned const max_char = u.max_char();
        auto& re = u.re;

        if (re.is_empty(r)) {
            out = range_predicate::empty(max_char);
            return true;
        }
        if (re.is_full_char(r)) {
            out = range_predicate::top(max_char);
            return true;
        }
        unsigned lo = 0, hi = 0;
        expr* lo_e = nullptr;
        expr* hi_e = nullptr;
        if (re.is_range(r, lo_e, hi_e)) {
            auto extract_char = [&](expr* e, unsigned& c) -> bool {
                if (u.is_const_char(e, c)) return true;
                expr* inner = nullptr;
                if (u.str.is_unit(e, inner) && u.is_const_char(inner, c)) return true;
                zstring s;
                if (u.str.is_string(e, s) && s.length() == 1) {
                    c = s[0];
                    return true;
                }
                return false;
            };
            if (!extract_char(lo_e, lo) || !extract_char(hi_e, hi))
                return false;
            // Empty/inverted range [lo > hi] is the empty regex.
            if (lo > hi) {
                out = range_predicate::empty(max_char);
                return true;
            }
            out = range_predicate::range(lo, hi, max_char);
            return true;
        }
        expr *a = nullptr, *b = nullptr, *c = nullptr;
        if (re.is_union(r, a, b)) {
            range_predicate pa(max_char), pb(max_char);
            if (!regex_to_range_predicate(u, a, pa)) return false;
            if (!regex_to_range_predicate(u, b, pb)) return false;
            out = pa | pb;
            return true;
        }
        auto mk_diff = [&](expr *a, expr *b) -> bool {
            range_predicate pa(max_char), pb(max_char);
            if (!regex_to_range_predicate(u, a, pa))
                return false;
            if (!regex_to_range_predicate(u, b, pb))
                return false;
            out = pa - pb;
            return true;
        };
        if (re.is_diff(r, a, b))
            return mk_diff(a, b);

        if (re.is_intersection(r, a, b) && re.is_complement(b, c)) 
            return mk_diff(a, c);
        
        if (re.is_intersection(r, a, b) && re.is_complement(a, c)) 
            return mk_diff(b, c);
        
        if (re.is_intersection(r, a, b)) {
            range_predicate pa(max_char), pb(max_char);
            if (!regex_to_range_predicate(u, a, pa)) return false;
            if (!regex_to_range_predicate(u, b, pb)) return false;
            out = pa & pb;
            return true;
        }

        
        // NOTE: re.complement is intentionally NOT handled here.
        //   re.complement is the SEQUENCE-level complement: its language
        //   includes the empty string, strings of length >= 2, and any
        //   length-1 string outside the operand.  A character-class
        //   range_predicate can only describe a set of length-1 strings,
        //   so collapsing re.complement(R) to ~R (character-level
        //   complement) would change semantics whenever R is wrapped in
        //   any sequence-level context (e.g. re.diff at the top level,
        //   or membership tests).  De-Morgan equivalences and the
        //   special cases re.complement(re.empty) / re.complement(re.full)
        //   are already handled directly in seq_rewriter::mk_re_complement.
        return false;
    }

    static expr_ref mk_unit_string_from_char(seq_util& u, unsigned c) {
        return expr_ref(u.str.mk_string(zstring(c)), u.get_manager());
    }

    static expr_ref mk_single_range_regex(seq_util& u, unsigned lo, unsigned hi, sort* re_sort) {
        ast_manager& m = u.get_manager();
        return expr_ref(u.re.mk_range(re_sort, lo, hi), m);
    }

    expr_ref range_predicate_to_regex(seq_util& u, range_predicate const& p, sort* seq_sort) {
        ast_manager& m = u.get_manager();
        sort* re_sort = u.re.mk_re(seq_sort);
        if (p.is_empty())
            return expr_ref(u.re.mk_empty(re_sort), m);
        unsigned const n = p.num_ranges();
        SASSERT(n > 0);
        if (n == 1) {
            auto [lo, hi] = p[0];
            return mk_single_range_regex(u, lo, hi, re_sort);
        }
        // Build single-range AST nodes first, then sort by expression id
        // so the resulting right-associated union matches the canonical
        // id-sorted shape that seq_rewriter::merge_regex_sets expects.
        // Without this the merge algorithm produces incorrect unions
        // when it has to combine our materialized output with another
        // (id-sorted) regex set.
        expr_ref_vector ranges(m);
        for (unsigned i = 0; i < n; ++i) {
            auto [lo, hi] = p[i];
            ranges.push_back(mk_single_range_regex(u, lo, hi, re_sort));
        }
        std::sort(ranges.data(), ranges.data() + ranges.size(),
                  [](expr* a, expr* b) { return a->get_id() < b->get_id(); });
        expr_ref acc(ranges.get(n - 1), m);
        for (unsigned i = n - 1; i-- > 0; )
            acc = expr_ref(u.re.mk_union(ranges.get(i), acc), m);
        return acc;
    }

}
