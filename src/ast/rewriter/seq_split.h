/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_split.h

Abstract:

    Regex split decomposition: the split function sigma from the paper
    "Solving by Splitting".  For a regular expression r, sigma(r) is a finite
    "split-set" of pairs { <D_i, N_i> } such that

        u.v in L(r)   iff   exists i:  u in L(D_i)  and  v in L(N_i).

    This lifts the decomposition previously buried in the nseq solver
    (seq::compute_sigma over euf::snode) into a self-contained, expr*-based
    engine that can be reused anywhere a seq_rewriter is available (the legacy
    seq solver, nseq, and the regex rewriter itself).

    The split algebra (intersection, De Morgan complement, left/right
    concatenation with a regex) and the cardinality-reducing simplification
    heuristics (drop bottom, same-D/same-N merge, subsumption via seq_subset)
    follow the paper.

Author:

    Nikolaj Bjorner (nbjorner) 2026-6-10
    Clemens Eisenhofer 2026-6-10

--*/
#pragma once

#include "ast/seq_decl_plugin.h"
#include "ast/rewriter/seq_subset.h"

class seq_rewriter;

// An individual split <D, N>: the left (prefix) regex D and right (suffix)
// regex N.  u.v in L(r) for this split iff u in L(D) and v in L(N).
struct split_pair {
    expr_ref m_d;
    expr_ref m_n;
    split_pair(expr* d, expr* n, ast_manager& m) : m_d(d, m), m_n(n, m) {
        SASSERT(d && n);
    }
};

// A split-set is a union of individual splits.
typedef vector<split_pair> split_set;

// Controls how aggressively sigma expands the Boolean-closure cases:
//   strong - fully expand complement / intersection via the split algebra
//            (De Morgan / cross product).  This is the behaviour the nseq
//            solver relies on.
//   weak   - do not perform the (potentially 2^k) Boolean-closure expansion;
//            give up (return false) on complement / intersection instead.
enum class split_mode { weak, strong };

class seq_split {
    seq_rewriter& m_rw;       // for mk_re_append + manager / seq_util access
    seq_subset    m_subset;   // language-subset checks for subsumption

    ast_manager&   m() const;
    seq_util&      seq() const;
    seq_util::rex& re() const;

    // S1 cap S2 = { <D1 cap D2, N1 cap N2> } dropping any pair with a bottom
    // component.  Returns false on threshold overrun.
    bool intersect(split_set const& s1, split_set const& s2, split_set& result, unsigned threshold);

    // De Morgan complement of a split-set: ~S = cap_{s in S} ~s with
    //   ~<D,N> = { <~D, .*>, <.*, ~N> }  and  ~{} = { <.*, .*> }.
    bool complement(sort* seq_sort, split_set const& sp, split_set& result, unsigned threshold);

    // same-D / same-N merge: groups pairs that share a (syntactically identical)
    // left (resp. right) component and unions the other component.
    void merge_by(split_set& pairs, bool by_left) const;

public:
    explicit seq_split(seq_rewriter& rw);

    // Compute sigma(r), appending to `out` (does not clear it).  `threshold`
    // bounds the number of produced splits; an overrun, an unsupported regex
    // shape (bounded loop / ite), or a Boolean-closure case in weak mode makes
    // it return false ("give up").
    bool compute(expr* r, split_set& out, unsigned threshold, split_mode mode = split_mode::strong);

    // In-place simplification of a split-set: drop bottom components, apply the
    // same-D / same-N merge rules, and drop splits subsumed by another (using
    // seq_subset).  Size-capped to keep the O(n^2) subsumption affordable.
    void simplify(split_set& s);
};
