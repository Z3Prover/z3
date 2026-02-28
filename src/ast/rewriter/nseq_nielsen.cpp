/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    nseq_nielsen.cpp

Abstract:

    Nielsen transformation-based word equation solver.

Author:

    Clemens Eisenhofer
    Nikolaj Bjorner (nbjorner) 2025-2-28

--*/

#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include "ast/rewriter/nseq_nielsen.h"

namespace seq {

    nielsen::nielsen(ast_manager& m, seq_rewriter& rw)
        : m(m), m_util(m), m_autil(m), m_rw(rw), m_lhs(m), m_rhs(m) {
    }

    bool nielsen::is_var(expr* e) const {
        return m_util.is_seq(e) &&
               !m_util.str.is_concat(e) &&
               !m_util.str.is_unit(e) &&
               !m_util.str.is_empty(e) &&
               !m_util.str.is_string(e);
    }

    bool nielsen::is_unit(expr* e) const {
        return m_util.str.is_unit(e);
    }

    bool nielsen::is_empty(expr* e) const {
        return m_util.str.is_empty(e);
    }

    bool nielsen::has_var(expr_ref_vector const& es) const {
        for (expr* e : es)
            if (is_var(e))
                return true;
        return false;
    }

    // -------------------------------------------------------
    // Strip matching constants/units from equation sides
    // -------------------------------------------------------

    bool nielsen::strip_common_prefix(expr_ref_vector& lhs, expr_ref_vector& rhs) {
        unsigned i = 0;
        unsigned min_sz = std::min(lhs.size(), rhs.size());
        while (i < min_sz) {
            expr* l = lhs.get(i);
            expr* r = rhs.get(i);
            // Both must be ground/unit and equal
            if (l == r && (is_unit(l) || m_util.str.is_string(l))) {
                i++;
                continue;
            }
            // Check if both are string constants with matching prefix
            zstring s1, s2;
            if (m_util.str.is_string(l, s1) && m_util.str.is_string(r, s2)) {
                if (s1 == s2) { i++; continue; }
            }
            break;
        }
        if (i == 0) return false;
        expr_ref_vector new_lhs(m), new_rhs(m);
        new_lhs.append(lhs.size() - i, lhs.data() + i);
        new_rhs.append(rhs.size() - i, rhs.data() + i);
        lhs.swap(new_lhs);
        rhs.swap(new_rhs);
        return true;
    }

    bool nielsen::strip_common_suffix(expr_ref_vector& lhs, expr_ref_vector& rhs) {
        unsigned li = lhs.size();
        unsigned ri = rhs.size();
        unsigned stripped = 0;
        while (li > 0 && ri > 0) {
            expr* l = lhs.get(li - 1);
            expr* r = rhs.get(ri - 1);
            if (l == r && (is_unit(l) || m_util.str.is_string(l))) {
                li--; ri--; stripped++;
                continue;
            }
            zstring s1, s2;
            if (m_util.str.is_string(l, s1) && m_util.str.is_string(r, s2)) {
                if (s1 == s2) { li--; ri--; stripped++; continue; }
            }
            break;
        }
        if (stripped == 0) return false;
        lhs.resize(li);
        rhs.resize(ri);
        return true;
    }

    // -------------------------------------------------------
    // Main simplification (no case splitting)
    // -------------------------------------------------------

    nielsen_result nielsen::simplify(expr_ref_vector& lhs, expr_ref_vector& rhs) {
        bool changed = false;

        // Remove empty strings from both sides
        unsigned j = 0;
        for (unsigned i = 0; i < lhs.size(); ++i)
            if (!is_empty(lhs.get(i)))
                lhs[j++] = lhs.get(i);
        lhs.resize(j);

        j = 0;
        for (unsigned i = 0; i < rhs.size(); ++i)
            if (!is_empty(rhs.get(i)))
                rhs[j++] = rhs.get(i);
        rhs.resize(j);

        // Loop until fixpoint: strip prefix/suffix, then leading/trailing vars
        bool progress = true;
        while (progress) {
            progress = false;

            // Check trivial cases
            if (lhs.empty() && rhs.empty())
                return nielsen_result::solved;

            // Strip common prefix and suffix (units and string constants)
            progress |= strip_common_prefix(lhs, rhs);
            progress |= strip_common_suffix(lhs, rhs);

            if (lhs.empty() && rhs.empty())
                return nielsen_result::solved;

            // Check for conflict: both sides start with different constants
            if (is_conflict(lhs, rhs))
                return nielsen_result::conflict;

            // Both sides start with the same variable: strip it
            if (!lhs.empty() && !rhs.empty() && lhs.get(0) == rhs.get(0) && is_var(lhs.get(0))) {
                expr_ref_vector new_lhs(m), new_rhs(m);
                new_lhs.append(lhs.size() - 1, lhs.data() + 1);
                new_rhs.append(rhs.size() - 1, rhs.data() + 1);
                lhs.swap(new_lhs);
                rhs.swap(new_rhs);
                progress = true;
                changed = true;
            }

            // Both sides end with the same variable: strip it
            if (!lhs.empty() && !rhs.empty() &&
                lhs.back() == rhs.back() && is_var(lhs.back())) {
                lhs.pop_back();
                rhs.pop_back();
                progress = true;
                changed = true;
            }

            changed |= progress;
        }

        if (lhs.empty() && rhs.empty())
            return nielsen_result::solved;

        // Variable = empty: if one side is empty and other has single var
        if (lhs.empty() && rhs.size() == 1 && is_var(rhs.get(0)))
            return nielsen_result::solved;  // x = ε is a solution
        if (rhs.empty() && lhs.size() == 1 && is_var(lhs.get(0)))
            return nielsen_result::solved;  // x = ε is a solution

        // Single variable = single term (x = t): a direct assignment, solved
        if (lhs.size() == 1 && is_var(lhs.get(0)) && !has_var(rhs))
            return nielsen_result::solved;
        if (rhs.size() == 1 && is_var(rhs.get(0)) && !has_var(lhs))
            return nielsen_result::solved;

        if (changed)
            return nielsen_result::reduced;

        return nielsen_result::unchanged;
    }

    // -------------------------------------------------------
    // Check for conflicts
    // -------------------------------------------------------

    bool nielsen::is_conflict(expr_ref_vector const& lhs, expr_ref_vector const& rhs) const {
        if (lhs.empty() != rhs.empty()) {
            // One side empty, other side has constants
            expr_ref_vector const& nonempty = lhs.empty() ? rhs : lhs;
            for (unsigned i = 0; i < nonempty.size(); ++i) {
                zstring s;
                if (m_util.str.is_string(nonempty[i], s) && s.length() > 0)
                    return true;
                if (is_unit(nonempty[i]))
                    return true;
            }
            return false;
        }
        if (lhs.empty() && rhs.empty())
            return false;

        // Both start with different non-variable ground terms
        expr* l = lhs[0];
        expr* r = rhs[0];
        zstring s1, s2;
        if (m_util.str.is_string(l, s1) && m_util.str.is_string(r, s2)) {
            if (s1.length() > 0 && s2.length() > 0 && s1[0] != s2[0])
                return true;
        }
        if (is_unit(l) && is_unit(r) && l != r) {
            // Only conflict if both are concrete character values that differ
            unsigned v1, v2;
            if (m_util.is_const_char(to_app(l)->get_arg(0), v1) &&
                m_util.is_const_char(to_app(r)->get_arg(0), v2) && v1 != v2)
                return true;
        }
        return false;
    }

    bool nielsen::is_solved(expr_ref_vector const& lhs, expr_ref_vector const& rhs) const {
        return lhs.empty() && rhs.empty();
    }

    // -------------------------------------------------------
    // Case splitting
    // -------------------------------------------------------

    void nielsen::apply_subst(expr* var, expr* term, expr_ref_vector const& src, expr_ref_vector& dst) {
        dst.reset();
        for (unsigned i = 0; i < src.size(); ++i) {
            if (src[i] == var) {
                // Replace variable with its substitution
                m_util.str.get_concat_units(term, dst);
            }
            else {
                dst.push_back(src[i]);
            }
        }
    }

    bool nielsen::split(expr_ref_vector const& lhs, expr_ref_vector const& rhs,
                        vector<nielsen_branch>& branches) {
        if (lhs.empty() || rhs.empty()) {
            // One side empty: all variables on other side must be empty
            expr_ref_vector const& nonempty = lhs.empty() ? rhs : lhs;
            for (unsigned i = 0; i < nonempty.size(); ++i) {
                if (is_var(nonempty[i])) {
                    nielsen_branch b(m);
                    b.var = nonempty[i];
                    b.term = m_util.str.mk_empty(nonempty[i]->get_sort());
                    // After substitution, just remove the empty variable
                    expr_ref_vector const& other = lhs.empty() ? lhs : rhs;
                    b.new_lhs.append(other);
                    for (unsigned j = 0; j < nonempty.size(); ++j)
                        if (j != i && !is_empty(nonempty[j]))
                            b.new_rhs.push_back(nonempty[j]);
                    if (lhs.empty()) b.new_lhs.swap(b.new_rhs);
                    branches.push_back(std::move(b));
                    return true;
                }
            }
            return false;
        }

        expr* l0 = lhs[0];
        expr* r0 = rhs[0];

        // Case 1: Variable vs constant/unit
        // x·α = c·β → branch: x = ε or x = c·x'
        if (is_var(l0) && (is_unit(r0) || m_util.str.is_string(r0))) {
            // Branch 1: x = ε
            {
                nielsen_branch b(m);
                b.var = l0;
                b.term = m_util.str.mk_empty(l0->get_sort());
                apply_subst(l0, b.term, lhs, b.new_lhs);
                b.new_rhs.append(rhs);
                branches.push_back(std::move(b));
            }
            // Branch 2: x = r0 · x' (peel first character)
            {
                nielsen_branch b(m);
                b.var = l0;
                expr_ref x_prime(m.mk_fresh_const("x", l0->get_sort()), m);
                b.term = m_util.str.mk_concat(r0, x_prime);
                apply_subst(l0, b.term, lhs, b.new_lhs);
                b.new_rhs.append(rhs);
                branches.push_back(std::move(b));
            }
            return true;
        }

        // Symmetric: constant vs variable on left
        if (is_var(r0) && (is_unit(l0) || m_util.str.is_string(l0))) {
            // Branch 1: y = ε
            {
                nielsen_branch b(m);
                b.var = r0;
                b.term = m_util.str.mk_empty(r0->get_sort());
                b.new_lhs.append(lhs);
                apply_subst(r0, b.term, rhs, b.new_rhs);
                branches.push_back(std::move(b));
            }
            // Branch 2: y = l0 · y'
            {
                nielsen_branch b(m);
                b.var = r0;
                expr_ref y_prime(m.mk_fresh_const("y", r0->get_sort()), m);
                b.term = m_util.str.mk_concat(l0, y_prime);
                b.new_lhs.append(lhs);
                apply_subst(r0, b.term, rhs, b.new_rhs);
                branches.push_back(std::move(b));
            }
            return true;
        }

        // Case 2: Variable vs variable
        // x·α = y·β → branch: x = y (if same), x = y·z, or y = x·z
        if (is_var(l0) && is_var(r0)) {
            if (l0 == r0) {
                // Same variable: strip and continue (should have been handled by simplify)
                return false;
            }
            // Branch 1: x = ε
            {
                nielsen_branch b(m);
                b.var = l0;
                b.term = m_util.str.mk_empty(l0->get_sort());
                apply_subst(l0, b.term, lhs, b.new_lhs);
                b.new_rhs.append(rhs);
                branches.push_back(std::move(b));
            }
            // Branch 2: y = ε
            {
                nielsen_branch b(m);
                b.var = r0;
                b.term = m_util.str.mk_empty(r0->get_sort());
                b.new_lhs.append(lhs);
                apply_subst(r0, b.term, rhs, b.new_rhs);
                branches.push_back(std::move(b));
            }
            // Branch 3: x = y · z (x is longer)
            {
                nielsen_branch b(m);
                b.var = l0;
                expr_ref z(m.mk_fresh_const("z", l0->get_sort()), m);
                b.term = m_util.str.mk_concat(r0, z);
                apply_subst(l0, b.term, lhs, b.new_lhs);
                b.new_rhs.append(rhs);
                branches.push_back(std::move(b));
            }
            // Branch 4: y = x · z (y is longer)
            {
                nielsen_branch b(m);
                b.var = r0;
                expr_ref z(m.mk_fresh_const("z", r0->get_sort()), m);
                b.term = m_util.str.mk_concat(l0, z);
                b.new_lhs.append(lhs);
                apply_subst(r0, b.term, rhs, b.new_rhs);
                branches.push_back(std::move(b));
            }
            return true;
        }

        return false;
    }
}
