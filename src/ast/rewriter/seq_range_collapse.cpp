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

    // Cofactor path condition `pred` (a Boolean over x = (:var 0)) -> the canonical
    // range_predicate (union of ranges) of the characters satisfying it.  Returns
    // false on a construct outside {true,false,and,or,not,=,char.<=} over x.
    static bool pred_to_rp(ast_manager &m, seq_util &sq, expr *x, expr *pred,
                           seq::range_predicate &out) {
        unsigned maxc = sq.max_char();
        expr *a = nullptr, *b = nullptr;
        unsigned c = 0;
        if (m.is_true(pred)) {
            out = seq::range_predicate::top(maxc);
            return true;
        }
        if (m.is_false(pred)) {
            out = seq::range_predicate::empty(maxc);
            return true;
        }
        if (m.is_eq(pred, a, b)) {
            if (a == x && sq.is_const_char(b, c)) {
                out = seq::range_predicate::singleton(c, maxc);
                return true;
            }
            if (b == x && sq.is_const_char(a, c)) {
                out = seq::range_predicate::singleton(c, maxc);
                return true;
            }
            return false;
        }
        if (sq.is_char_le(pred, a, b)) {
            if (b == x && sq.is_const_char(a, c)) {
                out = seq::range_predicate::range(c, maxc, maxc);
                return true;
            }
            if (a == x && sq.is_const_char(b, c)) {
                out = seq::range_predicate::range(0, c, maxc);
                return true;
            }
            return false;
        }
        if (m.is_not(pred, a)) {
            seq::range_predicate s(maxc);
            if (!pred_to_rp(m, sq, x, a, s))
                return false;
            out = ~s;
            return true;
        }
        if (m.is_and(pred)) {
            out = seq::range_predicate::top(maxc);
            for (expr *arg : *to_app(pred)) {
                seq::range_predicate s(maxc);
                if (!pred_to_rp(m, sq, x, arg, s))
                    return false;
                out = out & s;
            }
            return true;
        }
        if (m.is_or(pred)) {
            out = seq::range_predicate::empty(maxc);
            for (expr *arg : *to_app(pred)) {
                seq::range_predicate s(maxc);
                if (!pred_to_rp(m, sq, x, arg, s))
                    return false;
                out = out | s;
            }
            return true;
        }
        return false;
    }

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
        auto &m = u.get_manager();

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
            if (!regex_to_range_predicate(u, a, pa)) 
                return false;
            if (!regex_to_range_predicate(u, b, pb)) 
                return false;
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
            if (!regex_to_range_predicate(u, a, pa)) 
                return false;
            if (!regex_to_range_predicate(u, b, pb)) 
                return false;
            out = pa & pb;
            return true;
        }

        if (re.is_of_pred(r, a) && is_lambda(a)) {
            auto q = to_quantifier(a);
            if (q->get_num_decls() != 1)
                return false;
            auto body = q->get_expr();
            sort *char_sort = q->get_decl_sort(0);
            expr_ref var(m.mk_var(0, char_sort), m);
            if (u.get_char_plugin().get_family_id() == char_sort->get_family_id() && pred_to_rp(m, u, var, body, out))
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
        sort *char_sort = nullptr;
        VERIFY(u.is_seq(seq_sort, char_sort));
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
        expr_ref bound(m.mk_var(0, char_sort), m);
        symbol char_sym("ch");
        auto &ch = u.get_char_plugin();
        for (unsigned i = 0; i < n; ++i) {
            auto [lo, hi] = p[i];
            ranges.push_back(m.mk_and(ch.mk_le(ch.mk_char(lo), bound), ch.mk_le(bound, ch.mk_char(hi))));
        }
        expr_ref body(m.mk_or(ranges), m);
        return expr_ref(m.mk_lambda(1, &char_sort, &char_sym, body), m);
    }

    expr_ref unfold_fold(seq_rewriter &rw, expr *r) {
        auto &m = rw.m();
        auto& u = rw.u();
        expr_ref_pair_vector cofactors(m);  
        rw.brz_derivative_cofactors(r, cofactors);
        if (cofactors.empty()) 
            return expr_ref(u.re.mk_empty(r->get_sort()), m);
        
        sort *seq_sort = nullptr, *char_sort = nullptr;
        VERIFY(u.is_re(r, seq_sort));
        VERIFY(u.is_seq(seq_sort, char_sort));
        expr_ref var(m.mk_var(0, char_sort), m);
        expr_ref result(m);
        symbol ch("ch");
        for (auto const &[c, cof] : cofactors) {
            auto prefix = u.re.mk_of_pred(m.mk_lambda(1, &char_sort, &ch, c));
            auto term = u.re.mk_concat(prefix, cof);
            if (result) 
                result = u.re.mk_union(term, result);            
            else 
                result = term;                   
        }
        return result;
    }

}
