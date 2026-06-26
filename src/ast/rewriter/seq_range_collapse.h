/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_range_collapse.h

Abstract:

    Recognize regexes that are boolean combinations of character-class
    primitives (re.empty, re.full_char, re.range with concrete chars,
    and re.union/inter/comp/diff over translatable arguments), and
    materialize a seq::range_predicate back into a canonical regex AST.

    Together with seq_rewriter integration, this lets any boolean
    combination of character-class regexes collapse to a canonical
    multi-range form, so that equivalent character classes share AST
    identity, and downstream consumers (derivative, OneStep, caching)
    can short-circuit them as pure range predicates.

Authors:

    Margus Veanes (veanes) 2026

--*/
#pragma once

#include "ast/rewriter/seq_range_predicate.h"
#include "ast/seq_decl_plugin.h"

namespace seq {

    /**
     * If r is a boolean combination of character-class regex primitives
     * over the unsigned character domain [0, max_char], compute the
     * equivalent range_predicate and return true. Otherwise return false
     * with out untouched.
     *
     * Recognized fragment (all character-class-preserving operations):
     *   re.empty                              -> empty
     *   re.full_char_set                      -> top
     *   re.range "c_lo" "c_hi"  (concrete)    -> [c_lo, c_hi]
     *   re.union r1 r2                        -> p1 | p2
     *   re.intersection r1 r2                 -> p1 & p2
     *   re.diff r1 r2                         -> p1 - p2
     *
     * Notably re.complement is NOT recognized: it is a SEQUENCE-level
     * complement (over all of Σ*), not a character-class complement, so
     * collapsing it would change semantics whenever the result is used
     * in any non-character-class context.  Sequence-level rewrites for
     * re.complement (double-comp, deMorgan, etc.) are handled directly
     * in seq_rewriter::mk_re_complement.
     */
    bool regex_to_range_predicate(seq_util& u, expr* r, range_predicate& out);

    /**
     * Canonical materialization of p as a regex AST over the given
     * sequence sort. Two range_predicates with equal canonical
     * representations produce structurally identical regex ASTs:
     *
     *   empty                  -> re.empty
     *   top                    -> re.full_char_set
     *   single range [lo, hi]  -> re.range "lo" "hi"
     *   multiple ranges        -> right-associated re.union of single
     *                              ranges, in increasing order of lo
     *                              (matching the canonical range order
     *                              held by range_predicate).
     */
    expr_ref range_predicate_to_regex(seq_util& u, range_predicate const& p, sort* seq_sort);

}
