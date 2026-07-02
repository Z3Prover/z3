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

// Optional lookahead oracle.  Called for each candidate split <D, N> as it is
// generated; returns true to keep it, false to prune it.  An empty oracle (the
// default) keeps everything, so sigma is unchanged.  See seq_split::compute.
typedef std::function<bool(expr *D, expr *N)> split_oracle;

class split_set {
    struct imp;
    imp *m_imp;

    class consumer;

public:
    split_set(seq_rewriter &rw, expr *r, unsigned threshold, split_oracle const& filter);

    ~split_set();

    split_set(split_set const& other);

    class iterator {
        struct imp;
        imp *m_imp;
        friend class consumer;
    public:
        iterator(split_set const& s, bool end = false);
        ~iterator();
        iterator &operator++();
        std::pair<expr_ref, expr_ref> operator*() const;
        bool failed() const;
        bool operator==(iterator const &other) const;
        bool operator!=(iterator const &other) const {
            return !(*this == other);
        }
    };

    iterator begin() const;
    iterator end() const;
};
