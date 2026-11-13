/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    guard_set.h

Abstract:

    Sort-relative predicate algebra and an incremental conjunction accumulator.
    Character predicates use exact ranges. Bool and enumeration predicates use
    their exact domains; arithmetic, bit-vector and String equality predicates use
    mentioned values and a remaining-region representative. Unsupported theory
    reasoning returns unknown, never an assumed emptiness or witness.

    Extracted from seq_monadic.cpp.

Author:

    Nikolaj Bjorner / Margus Veanes 2026

--*/
#pragma once

#include "ast/ast.h"
#include "ast/seq_decl_plugin.h"
#include "ast/rewriter/seq_range_collapse.h"


class guard_set;

namespace seq {

class predicate_algebra {
public:
    // Cache mapping guard expressions to their range predicates.
    // A null value in the map records that the guard is unsupported (avoiding retranslation).
    // m_fresh recycles the last allocated range_predicate so failed translations do not
    // incur an alloc/dealloc cycle on every miss.
    //
    // Lifetime contract: expr* keys are assumed to outlive the cache (their lifetime is
    // managed by the caller -- e.g. by the cofactor_cache that owns the guard expressions).
    class cache {
        expr_ref_vector m_trail;
        obj_map<expr, range_predicate *> m_cache;
        range_predicate *m_fresh = nullptr;

    public:
        cache(ast_manager &m) : m_trail(m) {}
        ~cache() {
            reset();
        }
        void reset();
        void maybe_reset(unsigned cap) {
            if (m_cache.size() > cap)
                reset();
        }
        // Returns true if g is in the cache; val is set to the cached entry
        // (val may be null = unsupported guard).
        bool find(expr *g, range_predicate *&val) const {
            return m_cache.find(g, val);
        }
        // Returns a range_predicate* ready for guard_to_range_predicate to write into.
        // Reuses the previously recycled object when available; otherwise allocates one.
        range_predicate *fresh(unsigned max_char);
        // Records g -> p.  If p is non-null (translation succeeded), ownership is transferred
        // to the cache and m_fresh is cleared.  If p is null (unsupported), the object
        // previously returned by fresh() is retained in m_fresh for the next translation.
        void insert(expr *g, range_predicate *p);
    };

private:
    ast_manager&         m;
    seq_util&            u;
    sort*                m_sort;
    expr*                m_v0;
    bool                 m_is_char;
    cache*               m_rp_cache = nullptr;

    void collect_consts(expr* g, ptr_vector<expr>& out) const;
    lbool eval_at(expr* g, expr* cand) const;
    // l_false proves domain exhaustion; l_undef means freshness is unsupported.
    lbool mk_fresh(ptr_vector<expr> const& consts, expr_ref& out) const;
    lbool generic_eval(expr* g, expr_ref* witness) const;
    bool conjoin_ranges(expr* g, range_predicate& accumulated) const;
    expr_ref from_ranges(range_predicate const& ranges) const;
    expr_ref from_values(expr_ref_vector const& values, bool complement) const;
    friend class ::guard_set;

public:
    predicate_algebra(ast_manager& m, seq_util& u, sort* elem_sort, expr* v0,
                      cache* cache = nullptr);

    expr_ref mk_top() const { return expr_ref(m.mk_true(), m); }
    expr_ref mk_bottom() const { return expr_ref(m.mk_false(), m); }
    expr_ref mk_and(expr* a, expr* b) const;
    expr_ref mk_or(expr* a, expr* b) const;
    expr_ref mk_not(expr* a) const;

    // Equal canonical backend values materialize as the same AST. Unsupported
    // predicates retain their syntax; normalization never assumes parameters
    // are distinct or fixes their interpretation.
    expr_ref normalize(expr* predicate) const;

    // Strict total representation order within one AST manager, not implication.
    // Normalize first to identify equal backend values; then preserve AST-ID order.
    static bool less(expr* a, expr* b) { return a->get_id() < b->get_id(); }

    // l_false proves emptiness; l_true supplies a witness valid without new
    // assumptions about shared parameters. Otherwise return l_undef.
    lbool eval(expr* predicate, expr_ref* witness = nullptr) const;
};

}

class guard_set {
    seq::predicate_algebra m_algebra;
    bool m_is_char;
    bool m_ok = true;
    seq::range_predicate m_rp;
    expr_ref m_guard;

public:
    using cache = seq::predicate_algebra::cache;

    guard_set(ast_manager& _m, seq_util& _u, sort* elem_sort, expr* v0,
              cache* cache = nullptr);

    bool ok() const { return m_ok; }

    // AND in a cofactor guard g (a Boolean over v0).
    void conjoin(expr* g);

    // l_false = empty, l_true = non-empty (sets *witness if non-null to a justified
    // element of the set), l_undef = unknown / unsupported guard.
    lbool eval(expr_ref* witness) const;
};
