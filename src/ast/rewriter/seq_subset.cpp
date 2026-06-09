/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_subset.cpp

Abstract:

    Heuristic regular-expression subset checks used by seq_rewriter.

Author:

    Nikolaj Bjorner (nbjorner) 2026-6-8

--*/

#include "ast/rewriter/seq_subset.h"

bool seq_subset::is_subset_rec(expr* a, expr* b, unsigned depth) const {
    while (true) {
        
        if (a == b)
            return true;
        if (m_re.is_empty(a))
            return true;
        if (m_re.is_full_seq(b))
            return true;

        if (depth >= m_max_depth)
            return false;        

        expr* a1 = nullptr, * a2 = nullptr, *a3 = nullptr, * b1 = nullptr, * b2 = nullptr, * b3 = nullptr;
        unsigned la, ua, lb, ub;

        // a ⊆ .+ iff a is non-nullable
        if (m_re.is_dot_plus(b) && m_re.get_info(a).nullable == l_false)
            return true;

        // a ⊆ a*
        if (m_re.is_star(b, b1) && is_subset_rec(a, b1, depth))
            return true;

        // e ⊆ a*
        if (m_re.is_epsilon(a) && m_re.is_m_re.is_star(b, b1))
            return true;

        // E3: R ⊆ R*
        if (m_re.is_star(b, b1) && is_subset_rec(a, b1, depth + 1))
            return true;

        // E3: R1* ⊆ R2* if R1 ⊆ R2
        if (m_re.is_star(a, a1) && m_re.is_star(b, b1) && is_subset_rec(a1, b1, depth + 1))
            return true;

        // E3: R1+ ⊆ R2+ if R1 ⊆ R2
        if (m_re.is_plus(a, a1) && m_re.is_plus(b, b1) && is_subset_rec(a1, b1, depth))
            return true;

        // a ⊆ b1 ∪ b2 if a ⊆ b1 or a ⊆ b2
        if (m_re.is_union(b, b1, b2) && (is_subset_rec(a, b1, depth + 1) || is_subset_rec(a, b2, depth + 1)))
            return true;

        // a1 ∪ a2 ⊆ b if a1 ⊆ b and a2 ⊆ b
        if (m_re.is_union(a, a1, a2) && is_subset_rec(a1, b, depth + 1) && is_subset_rec(a2, b, depth + 1))
            return true;

        // a1 ∩ a2 ⊆ b if a1 ⊆ b or a2 ⊆ b
        if (m_re.is_intersection(a, a1, a2) && (is_subset_rec(a1, b, depth + 1) || is_subset_rec(a2, b, depth + 1)))
            return true;

        // a ⊆ b1 ∩ b2 if a ⊆ b1 and a ⊆ b2
        if (m_re.is_intersection(b, b1, b2) && is_subset_rec(a, b1, depth + 1) && is_subset_rec(a, b2, depth + 1))
            return true;

        // r1=ra3{la,ua}ra2, r2=rb3{lb,ub}rb2, ra3=rb3, lb<=la, ua<=ub
        if (re().is_concat(a, a1, a2) && re().is_loop(a1, a3, la, ua) &&
            re().is_concat(b, b1, b2) && re().is_loop(b1, b3, lb, ub) &&
            a3 == b3 && lb <= la && ua <= ub) {
            a = a2;
            b = b2;
            continue;
        }
        // ra1=ra3{la,ua}, r2=rb3{lb,ub}, ra3=rb3, lb<=la, ua<=ub
        if (re().is_loop(a, a1, la, ua) &&
            re().is_loop(b, b1, lb, ub) &&
            lb <= la && ua <= ub && is_subset_rec(a1, b1, depth + 1)) {
            return true;
        }        

        // concat monotonicity:
        // tail-recursive on second arguments (without increasing depth bound).
        if (m_re.is_concat(a, a1, a2) && m_re.is_concat(b, b1, b2) && is_subset_rec(a1, b1, depth + 1)) {
            a = a2;
            b = b2;
            continue;
        }

        // E2: R ⊆ Σ*·R' if R ⊆ R'
        if (m_re.is_concat(b, b1, b2) && m_re.is_full_seq(b1) && is_subset_rec(a, b2, depth))
            return true;

        // loop subsumption: r{la,ua} ⊆ r{lb,ub} when lb <= la and ua <= ub
        if (m_re.is_loop(a, a1, la, ua) && m_re.is_loop(b, b1, lb, ub) &&
            is_subset_rec(a1, b1, depth + 1) && lb <= la && ua <= ub)
            return true;

        // complement: ~a ⊆ ~b if b ⊆ a
        if (m_re.is_complement(a, a1) && m_re.is_complement(b, b1))
            return is_subset_rec(b1, a1, depth + 1);

        return false;
    }
}

bool seq_subset::is_subset(expr* a, expr* b) const {
    return is_subset_rec(a, b, 0);
}
