/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_split.h

Abstract:

    Regex split decomposition: the split function sigma from the paper
    "Solving by Splitting".  For a regular expression r, sigma(r) is a finite
    "split-set" of pairs { <D_i, N_i> } such that

        u.v in L(r)   iff   exists i:  u in L(D_i)  and  v in L(N_i).

    The split algebra (intersection, De Morgan complement, left/right
    concatenation with a regex) and the cardinality-reducing simplification
    heuristics (drop bottom, same-D/same-N merge, subsumption via seq_subset)
    follow the paper.

Author:

    Clemens Eisenhofer 2026-6-10

--*/
#pragma once

#include "ast/seq_decl_plugin.h"
#include "ast/rewriter/seq_subset.h"
#include <functional>

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

// Optional lookahead oracle.  Called for each candidate split <D, N> as it is
// generated; returns true to keep it, false to prune it.  An empty oracle (the
// default) keeps everything, so sigma is unchanged.  See seq_split::compute.
typedef std::function<bool(expr* D, expr* N)> split_oracle;

// Lightweight performance counters for the split algebra (surfaced via -st in
// the nseq solver; behaviour-neutral).  See seq_split.cpp for where each fires.
struct split_stats {
    unsigned m_make = 0;               // make(): suspended sigma(r) built
    unsigned m_sigma_expand = 0;       // expand_fromre(): one sigma rule level
    unsigned m_materialize = 0;        // materialize(): a split-set drained
    unsigned m_splits = 0;             // splits produced by iterator::next()
    unsigned m_pushes = 0;             // candidate <D,N> offered to push()
    unsigned m_oracle_prunes = 0;      // candidates dropped by the lookahead oracle
    unsigned m_intersect = 0;          // intersect() calls
    unsigned m_intersect_pairs = 0;    // pairs formed by intersect() cross-products
    unsigned m_complement = 0;         // complement() calls
    unsigned m_giveups = 0;            // iterator give-ups (unsupported/weak/overrun)
    unsigned m_threshold_overruns = 0; // threshold hits (intersect/complement/iterator)
    unsigned m_max_split_set = 0;      // largest materialized split-set seen
    unsigned m_dedup_drops = 0;        // duplicate <D,N> pairs skipped in intersect
    unsigned m_simplify = 0;           // simplify() calls
    void reset() { *this = split_stats(); }
};

class seq_split {
    ast_manager& m;
    seq_rewriter& m_rw;       // for mk_re_append + manager / seq_util access
    seq_subset    m_subset;   // language-subset checks for subsumption

    // --- Suspended split-set representation -------------------------------
    // A split-set computation is kept as an `expr` term over a small family of
    // locally-declared, uninterpreted function symbols (the split algebra of the
    // paper / split-algebra.md).  Nothing here is ever asserted to the solver;
    // the terms are only used as scratch structure to drive lazy expansion.
    //
    //   empty    : SplitSet                 -- {} (bottom)
    //   single   : Re x Re -> SplitSet       -- a single split <D, N>
    //   from_re  : Re -> SplitSet            -- the *suspended* sigma(r)
    //   union    : SplitSet x SplitSet -> SplitSet
    //   inter    : SplitSet x SplitSet -> SplitSet
    //   compl    : SplitSet -> SplitSet
    //   lcat     : Re x SplitSet -> SplitSet -- r . S (left-concat onto D)
    //   rcat     : SplitSet x Re -> SplitSet -- S . r (right-concat onto N)
    sort*         m_seq_sort = nullptr;   // sequence sort the decls are built for
    sort_ref      m_set_sort;             // the uninterpreted SplitSet sort
    func_decl_ref m_d_empty, m_d_single, m_d_fromre, m_d_union,
                  m_d_inter, m_d_compl, m_d_lcat, m_d_rcat;
    expr_ref      m_empty_app;            // cached nullary `empty` term
    mutable split_stats m_stats;          // performance counters (see -st)

    seq_util&      seq() const;
    seq_util::rex& re() const;

    // (Re)build the local declarations for `seq_sort` if not already current.
    void ensure_decls(sort* seq_sort);

    // Smart constructors: apply the cheap normalizations the eager engine relies
    // on (drop-bottom, eps cancellation, union absorption of empty).
    expr_ref mk_empty();
    expr_ref mk_single(expr* d, expr* n);
    expr_ref mk_fromre(expr* r);
    expr_ref mk_union(expr* a, expr* b);
    expr_ref mk_inter(expr* a, expr* b);
    expr_ref mk_compl(expr* a);
    expr_ref mk_lcat(expr* r, expr* s);
    expr_ref mk_rcat(expr* s, expr* r);

    // Recognizers over the local decls.
    bool is_empty_ss(expr* e) const;
    bool is_single(expr* e, expr*& d, expr*& n) const;
    bool is_fromre(expr* e, expr*& r) const;
    bool is_union (expr* e, expr*& a, expr*& b) const;
    bool is_inter (expr* e, expr*& a, expr*& b) const;
    bool is_compl (expr* e, expr*& a) const;
    bool is_lcat  (expr* e, expr*& r, expr*& s) const;
    bool is_rcat  (expr* e, expr*& s, expr*& r) const;
    // A term whose head is empty | single | union (ready for the worklist loop).
    bool is_frontier(expr* e) const;

    // One level of the sigma rules: from_re(r) -> a SplitSet term built from the
    // immediate subterms.  `ok` is set false on an unsupported shape.
    expr_ref expand_fromre(expr* r, bool& ok);
    // Distribute a left/right concatenation over a head-normal split-set.
    expr_ref distribute_lcat(expr* r, expr* hs);
    expr_ref distribute_rcat(expr* hs, expr* r);
    // Materialized split-set -> a `union` of `single`s.
    expr_ref from_split_set(split_set const& s);
    // Reduce `t` until its head is empty | single | union (one outermost level
    // for the lazy nodes; inter/compl are expanded eagerly via `materialize`,
    // since the paper's De Morgan / cross-product cannot yield a split lazily).
    // `ok` is set false on a give-up (unsupported shape, weak-mode Boolean, or
    // threshold overrun).
    expr_ref head_normalize(expr* t, split_mode mode, unsigned threshold,
                            split_oracle const& oracle, bool& ok);
    // Fully drain a suspended split-set into `out` (used for inter/compl bodies).
    // Runs an `iterator` to exhaustion; returns false on a give-up.
    bool materialize(expr* node, split_mode mode, unsigned threshold,
                     split_oracle const& oracle, split_set& out);

    // Push <d, n> onto `out`, unless `oracle` rejects it.
    void push(split_set& out, split_oracle const& oracle, expr* d, expr* n) const;

    // S1 cap S2 = { <D1 cap D2, N1 cap N2> } dropping any pair with a bottom
    // component (and any rejected by `oracle`).  Returns false on threshold overrun.
    bool intersect(split_set const& s1, split_set const& s2, split_set& result,
                   unsigned threshold, split_oracle const& oracle) const;

    // De Morgan complement of a split-set: ~S = cap_{s in S} ~s with
    //   ~<D,N> = { <~D, .*>, <.*, ~N> }  and  ~{} = { <.*, .*> }.
    bool complement(sort* seq_sort, split_set const& sp, split_set& result,
                    unsigned threshold, split_oracle const& oracle) const;

    // same-D / same-N merge: groups pairs that share a (syntactically identical)
    // left (resp. right) component and unions the other component.
    void merge_by(split_set& pairs, bool by_left) const;

public:
    explicit seq_split(seq_rewriter& rw);

    // Performance counters (read via nseq -st).
    split_stats const& stats() const { return m_stats; }
    void reset_stats() { m_stats.reset(); }

    // Lazy split enumerator.  Holds the suspended split-set worklist and produces
    // the concrete splits <D, N> one at a time, on demand, instead of computing
    // them all up front.  Obtain one from seq_split::iterate (or construct it
    // directly) and pull splits with next() until it returns false; gave_up() then
    // tells a normal exhaustion (false) apart from a give-up (true).
    //
    // The threshold is supplied by the caller and serves only as a safety cap
    // against space bloat (lazy expansion still has to materialize the operands of
    // intersection / complement).  A threshold overrun, an unsupported regex shape,
    // or a Boolean-closure case in weak mode aborts the enumeration: next() returns
    // false and gave_up() returns true.  To stop early, simply stop calling next().
    //
    // `oracle` (optional) prunes non-viable splits as they are produced.  It must
    // be sound to apply per split: a candidate N can still gain a prefix from a
    // factor appended to its right later (concat/star), so the oracle must use a
    // "prefix-compatible" test (prune only when N can never match the lookahead,
    // even partially), NOT a strict "starts-with" test.  The complement body is
    // expanded WITHOUT the oracle (inverted orientation); the oracle is re-applied
    // to the complement's output fold.
    class iterator {
        seq_split&      m_engine;
        ast_manager&    m;
        split_mode      m_mode;
        unsigned        m_threshold;
        split_oracle    m_oracle;
        expr_ref_vector m_work;        // GC-safe worklist of suspended split-sets
        unsigned        m_count = 0;   // splits produced so far (vs. threshold)
        bool            m_giveup = false;
    public:
        iterator(seq_split& engine, expr* node, split_mode mode,
                 unsigned threshold, split_oracle oracle);
        // Compute the next split.  On success returns true and sets <d, n>; on
        // exhaustion or give-up returns false (see gave_up()).  Calling next()
        // again after it has returned false keeps returning false.
        bool next(expr_ref& d, expr_ref& n);
        // Valid after next() has returned false: true iff the enumeration aborted
        // (unsupported regex / weak-mode Boolean / threshold overrun) rather than
        // running out of splits.
        bool gave_up() const { return m_giveup; }
    };

    // Build the *suspended* sigma(r) as a split-algebra term (no expansion).
    // Returns null on a non-regex argument.  Drive it with `iterate`.
    expr_ref make(expr* r);

    // Create a lazy enumerator over a suspended split-set `node` (typically the
    // result of make()).  See `iterator` for the meaning of the arguments.
    iterator iterate(expr* node, split_mode mode, unsigned threshold,
                     split_oracle const& oracle = {});

    // Compute sigma(r), appending to `out` (does not clear it).  Thin eager
    // wrapper that drains an `iterator` to exhaustion; semantics match the historic
    // engine.  See `iterator` for the meaning of `threshold`, `mode`, and `oracle`.
    bool compute(expr* r, split_set& out, unsigned threshold,
                 split_mode mode = split_mode::strong, split_oracle const& oracle = {});

    // In-place simplification of a split-set: drop bottom components, apply the
    // same-D / same-N merge rules, and drop splits subsumed by another (using
    // seq_subset).  Size-capped to keep the O(n^2) subsumption affordable.
    void simplify(split_set& s) const;

    // decompose a membership constraint into a set of pairs of regex splits
    std::pair<expr_ref, expr_ref> split_membership(expr* str, expr* regex, unsigned threshold, split_set& result) const;

    // Lookahead oracle for the split engine: is the split's right component
    // `n_regex` prefix-compatible with the constant character sequence `c`?
    // This is sound to apply during split generation — it never drops a viable split.
    // Thus, it might not eliminate all cases in order to stay sound
    bool split_lookahead_viable(expr* regex, zstring const& c) const;


};
