/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_nielsen_internal.h

Abstract:

    Implementation-private declarations shared by the seq_nielsen*.cpp
    translation units.  NOT part of the module interface -- nothing outside
    src/smt/seq/seq_nielsen*.cpp may include this file; use seq_nielsen.h.

    It is an umbrella include (every seq_nielsen*.cpp includes only this) plus
    the handful of helpers that genuinely cross file boundaries: direction
    folding, power accessors and the suspended factorization state.

Author:

    Clemens Eisenhofer 2026-03-02
    Nikolaj Bjorner (nbjorner) 2026-03-02

--*/

#pragma once

#include "smt/seq/seq_nielsen.h"
#include "smt/seq/seq_parikh.h"
#include "smt/seq/seq_regex.h"
#include "ast/arith_decl_plugin.h"
#include "ast/ast_pp.h"
#include "ast/ast_util.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/rewriter/seq_monadic.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/rewriter/seq_skolem.h"
#include "util/statistics.h"
#include <algorithm>
#include <cstdlib>
#include <stack>
#include <unordered_map>
#include <vector>

namespace seq {


    // Normalize an arithmetic expression using the caller's th_rewriter.
    // Simplifies e.g. (n - 1 + 1) to n, preventing unbounded growth
    // of power exponents during unwind/merge cycles.  Takes the rewriter as
    // an argument (nielsen_graph::m_rw) — constructing a th_rewriter per
    // call is far too expensive for these hot paths.
    inline expr_ref normalize_arith(th_rewriter &rw, expr *e) {
        expr_ref result(e, rw.m());
        rw(result);
        return result;
    }

    // Suspended state of a lazy regex factorization (apply_regex_factorization).
    // One rf_state drives the whole binary "remaining splits" chain for a single
    // membership: it owns the lazy split iterator and remembers the chosen
    // head/tail boundary plus the leading constant run consumed from the tail.
    struct rf_state {
        str_mem             m_mem;   // the membership being factorized (kept on child B)
        euf::snode const*   m_head;  // prefix boundary  (head ∈ Δ)
        euf::snode const*   m_tail;  // suffix boundary, const run already consumed (tail ∈ ∇)
        zstring             m_c;     // leading constant run consumed from the tail
        seq_split::iterator m_iter;  // lazy split enumerator, shared down the child-B chain
        rf_state(str_mem const& mem, euf::snode const* head, euf::snode const* tail,
                 zstring const& c, seq_split::iterator&& it) :
            m_mem(mem), m_head(head), m_tail(tail), m_c(c), m_iter(std::move(it)) {}
    };

    // Directional helpers:
    // fwd=true  -> left-to-right (prefix/head)
    // fwd=false -> right-to-left (suffix/tail)
    inline euf::snode const* dir_token(euf::snode const* s, const bool fwd) {
        if (!s)
            return nullptr;
        return fwd ? s->first() : s->last();
    }

    inline euf::snode const* dir_drop(euf::sgraph &sg, euf::snode const* s, const unsigned count, const bool fwd) {
        if (!s || count == 0)
            return s;
        return fwd ? sg.drop_left(s, count) : sg.drop_right(s, count);
    }

    inline euf::snode const* dir_concat(euf::sgraph &sg, euf::snode const* a, euf::snode const* b, const bool fwd) {
        if (!a)
            return b;
        if (!b)
            return a;
        return fwd ? sg.mk_concat(a, b) : sg.mk_concat(b, a);
    }

    inline void collect_tokens_dir(euf::snode const* s, const bool fwd, euf::snode_vector &toks) {
        toks.reset();
        if (!s)
            return;
        s->collect_tokens(toks);
        if (!fwd)
            toks.reverse();
    }

    // does `var` occur among the tokens of `s`?  Token iteration, not
    // collect_tokens: the occurrence checks run inside the modifier scan loops,
    // where materializing every side would dominate.
    inline bool snode_contains_var(euf::snode const* s, euf::snode const* var) {
        SASSERT(s && var);
        for (euf::snode const* t : *s) {
            if (t == var)
                return true;
        }
        return false;
    }

    // Deep occurrence check: does `var` occur anywhere in `n`, INCLUDING inside
    // power bases?  collect_tokens / snode_contains_var treat a power token as
    // opaque, so a variable nested inside a base is invisible to them - and a
    // substitution x -> u.(x)^n.v would pass for eliminating while its
    // |x| = |replacement| edge constraint degenerates to |x| = ... + n.|x|.
    inline bool deep_contains_var(euf::snode const* n, euf::snode const* var) {
        SASSERT(n && var);
        for (euf::snode const* t : *n) {
            if (t == var)
                return true;
            if (t->is_power() && t->arg0() && deep_contains_var(t->arg0(), var))
                return true;
        }
        return false;
    }

    // Get the base expression of a power snode.
    inline expr* get_power_base_expr(euf::snode const* power, seq_util& seq) {
        if (!power || !power->is_power()) return nullptr;
        const expr * e = power->get_expr();
        expr* base = nullptr, *exp = nullptr;
        return (e && seq.str.is_power(e, base, exp)) ? base : nullptr;
    }

    // Get the exponent expression of a power snode.
    inline expr* get_power_exp_expr(euf::snode const* power, seq_util& seq) {
        if (!power->is_power()) return nullptr;
        const expr * e = power->get_expr();
        expr* base = nullptr, *exp = nullptr;
        return (e && seq.str.is_power(e, base, exp)) ? exp : nullptr;
    }

    // Check if exponent b equals exponent a + diff for some rational constant.
    // Defined in seq_nielsen_simplify.cpp.
    bool get_const_power_diff(expr* b, expr* a, arith_util& arith, rational& diff);

    // CommPower: how many times does the base pattern of a power occur in the
    // directional prefix of `side`?  Returns (count_expr, tokens_consumed);
    // count_expr is null when no complete match is found.
    // Defined in seq_nielsen_simplify.cpp.
    std::pair<expr_ref, unsigned> comm_power(
            euf::snode const* base_sn, euf::snode const* side, ast_manager& m, arith_util& arith,
            seq_util& seq, const bool fwd);
}
