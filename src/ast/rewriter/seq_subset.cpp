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
        if (m_re.is_epsilon(a) && m_re.get_info(b).nullable == l_true)
            return true;

        if (depth >= m_max_depth)
            return false;        

        expr* a1 = nullptr, * a2 = nullptr, * b1 = nullptr, * b2 = nullptr;
        unsigned la, ua, lb, ub;

        // a ⊆ .+ iff a is non-nullable
        if (m_re.is_dot_plus(b) && m_re.get_info(a).nullable == l_false)
            return true;

        // a ⊆ a*
        if (m_re.is_star(b, b1) && is_subset_rec(a, b1, depth))
            return true;

        // e ⊆ a*
        if (m_re.is_epsilon(a) && m_re.is_star(b, b1))
            return true;

        // R ⊆ R*
        if (m_re.is_star(b, b1) && is_subset_rec(a, b1, depth + 1))
            return true;

        // R1* ⊆ R2* if R1 ⊆ R2
        if (m_re.is_star(a, a1) && m_re.is_star(b, b1) && is_subset_rec(a1, b1, depth + 1))
            return true;

        // R1+ ⊆ R2+ if R1 ⊆ R2
        if (m_re.is_plus(a, a1) && m_re.is_plus(b, b1) && is_subset_rec(a1, b1, depth))
            return true;

        // R ⊆ R+
        if (m_re.is_plus(b, b1) && is_subset_rec(a, b1, depth))
            return true;

        // R+ ⊆ R*
        if (m_re.is_plus(a, a1) && m_re.is_star(b, b1) && is_subset_rec(a1, b1, depth + 1))
            return true;

        // range containment
        if (m_re.is_range(a, la, ua) && m_re.is_range(b, lb, ub) && lb <= la && ua <= ub)
            return true;

        // to_re(s) ⊆ range
        if (m_re.is_to_re(a, a1) && m_re.is_range(b, lb, ub) && is_app(a1)) {
            func_decl* f = to_app(a1)->get_decl();
            if (f->get_decl_kind() == OP_STRING_CONST && f->get_num_parameters() == 1) {
                zstring const& s = f->get_parameter(0).get_zstring();
                if (s.length() == 1 && lb <= s[0] && s[0] <= ub)
                    return true;
            }
        }

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

        // R{la,ua} ⊆  R'{lb,ub} if  R ⊆ R', lb<=la, ua<=ub
        if (m_re.is_loop(a, a1, la, ua) &&
            m_re.is_loop(b, b1, lb, ub) &&
            lb <= la && ua <= ub && is_subset_rec(a1, b1, depth + 1)) {
            return true;
        }

        // a1 \ a2 ⊆ b if a1 ⊆ b
        if (m_re.is_diff(a, a1, a2) && is_subset_rec(a1, b, depth + 1))
            return true;

        // R ⊆ Σ*·R' if R ⊆ R'
        if (m_re.is_concat(b, b1, b2) && m_re.is_full_seq(b1) && is_subset_rec(a, b2, depth))
            return true;

        // R ⊆ R'·Σ* if R ⊆ R'
        if (m_re.is_concat(b, b1, b2) && m_re.is_full_seq(b2) && is_subset_rec(a, b1, depth))
            return true;

        // star absorption: R·R* ⊆ R*, R*·R ⊆ R*
        bool const is_concat_star = m_re.is_concat(a, a1, a2) && m_re.is_star(b, b1);
        if (is_concat_star &&
            is_subset_rec(a1, b1, depth + 1) && is_subset_rec(a2, b, depth + 1))
            return true;
        if (is_concat_star &&
            is_subset_rec(a2, b1, depth + 1) && is_subset_rec(a1, b, depth + 1))
            return true;

        // concat monotonicity:
        // tail-recursive on second arguments (without increasing depth bound).
        if (m_re.is_concat(a, a1, a2) && m_re.is_concat(b, b1, b2) && is_subset_rec(a1, b1, depth + 1)) {
            a = a2;
            b = b2;
            continue;
        }

        // complement: ~a ⊆ ~b if b ⊆ a
        if (m_re.is_complement(a, a1) && m_re.is_complement(b, b1))
            return is_subset_rec(b1, a1, depth + 1);

        return false;
    }
}

bool seq_subset::is_subset(expr* a, expr* b) const {
    return is_subset_rec(a, b, 0);
}
