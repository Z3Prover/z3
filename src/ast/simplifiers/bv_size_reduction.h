/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    bv_size_reduction.h

Abstract:

    Reduce the number of bits used to encode constants, by using signed bounds.
    Example: suppose x is a bit-vector of size 8, and we have
    signed bounds for x such that:
        -2 <= x <= 2
    Then, x can be replaced by  ((sign-extend 5) k)
    where k is a fresh bit-vector constant of size 3.

Author:

    Leonardo (leonardo) 2012-02-19

Notes:

    does not support proofs, nor unsat cores

--*/
#pragma once

#include "ast/simplifiers/dependent_expr_state.h"
#include "ast/bv_decl_plugin.h"
#include "ast/rewriter/expr_replacer.h"

class bv_size_reduction_simplifier : public dependent_expr_simplifier {
    typedef rational numeral;
    bv_util                   m_util;
    obj_map<app, numeral>     m_signed_lowers;
    obj_map<app, numeral>     m_signed_uppers;
    scoped_ptr<expr_replacer> m_replacer;

    void update_signed_lower(app* v, numeral const& k) {
        // k <= v
        auto& value = m_signed_lowers.insert_if_not_there(v, k);
        if (value < k)
            value = k;
    }

    void update_signed_upper(app* v, numeral const& k) {
        // v <= k
        auto& value = m_signed_uppers.insert_if_not_there(v, k);
        if (k < value)
            value = k;
    }

    void collect_bounds() {
        numeral val;
        unsigned bv_sz;
        expr *f, *lhs, *rhs;
        for (unsigned idx : indices()) {
            bool negated = false;
            f = m_fmls[idx].fml();
            if (m.is_not(f)) {
                negated = true;
                f = to_app(f)->get_arg(0);
            }
            if (m_util.is_bv_sle(f, lhs, rhs)) {
                bv_sz = m_util.get_bv_size(lhs);
                if (is_uninterp_const(lhs) && m_util.is_numeral(rhs, val, bv_sz)) {
                    // lhs <= rhs, i.e., v <= k
                    val = m_util.norm(val, bv_sz, true);
                    if (negated) {
                        // not (v <= k) means v >= k+1
                        val += numeral(1);
                        if (m_util.norm(val, bv_sz, true) == val)
                            update_signed_lower(to_app(lhs), val);
                    }
                    else
                        update_signed_upper(to_app(lhs), val);
                }
                else if (is_uninterp_const(rhs) && m_util.is_numeral(lhs, val, bv_sz)) {
                    // lhs <= rhs, i.e., k <= v
                    val = m_util.norm(val, bv_sz, true);
                    if (negated) {
                        // not (k <= v) means v <= k-1
                        val -= numeral(1);
                        if (m_util.norm(val, bv_sz, true) == val)
                            update_signed_upper(to_app(rhs), val);
                    }
                    else
                        update_signed_lower(to_app(rhs), val);
                }
            }
        }
    }

public:
    bv_size_reduction_simplifier(ast_manager& m, params_ref const& p, dependent_expr_state& s)
        : dependent_expr_simplifier(m, s),
          m_util(m),
          m_replacer(mk_default_expr_replacer(m, false)) {}

    char const* name() const override { return "reduce-bv-size"; }

    bool supports_proofs() const override { return false; }

    void reduce() override {
        m_signed_lowers.reset();
        m_signed_uppers.reset();
        m_replacer->reset();

        collect_bounds();
        if (m_signed_lowers.empty() || m_signed_uppers.empty())
            return;

        expr_substitution subst(m);

        for (auto& [k, lower_val] : m_signed_lowers) {
            unsigned bv_sz = m_util.get_bv_size(k);
            numeral l = m_util.norm(lower_val, bv_sz, true);
            obj_map<app, numeral>::obj_map_entry* entry = m_signed_uppers.find_core(k);
            if (!entry)
                continue;
            numeral u = m_util.norm(entry->get_data().m_value, bv_sz, true);
            expr* new_def = nullptr;
            app*  new_const = nullptr;
            if (l > u) {
                m_fmls.add(dependent_expr(m, m.mk_false(), nullptr, nullptr));
                return;
            }
            else if (l == u)
                new_def = m_util.mk_numeral(l, k->get_sort());
            else if (l.is_neg()) {
                unsigned l_nb = (-l).get_num_bits();
                if (u.is_neg()) {
                    // l <= v <= u <= 0
                    unsigned i_nb = l_nb;
                    if (i_nb < bv_sz) {
                        new_const = m.mk_fresh_const(nullptr, m_util.mk_sort(i_nb));
                        new_def = m_util.mk_concat(m_util.mk_numeral(numeral(-1), bv_sz - i_nb), new_const);
                    }
                }
                else {
                    // l <= v <= 0 <= u
                    unsigned u_nb = u.get_num_bits();
                    unsigned i_nb = std::max(l_nb, u_nb) + 1;
                    if (i_nb < bv_sz) {
                        new_const = m.mk_fresh_const(nullptr, m_util.mk_sort(i_nb));
                        new_def = m_util.mk_sign_extend(bv_sz - i_nb, new_const);
                    }
                }
            }
            else {
                // 0 <= l <= v <= u
                unsigned u_nb = u.get_num_bits();
                if (u_nb < bv_sz) {
                    new_const = m.mk_fresh_const(nullptr, m_util.mk_sort(u_nb));
                    new_def = m_util.mk_concat(m_util.mk_numeral(numeral(0), bv_sz - u_nb), new_const);
                }
            }
            if (!new_def)
                continue;
            subst.insert(k, new_def);
            m_fmls.model_trail().push(k->get_decl(), new_def, nullptr, {});
            if (new_const)
                m_fmls.model_trail().hide(new_const->get_decl());
        }

        if (subst.empty())
            return;

        m_replacer->set_substitution(&subst);
        expr_ref new_curr(m);
        for (unsigned idx : indices()) {
            auto const& d = m_fmls[idx];
            (*m_replacer)(d.fml(), new_curr);
            if (new_curr != d.fml())
                m_fmls.update(idx, dependent_expr(m, new_curr, nullptr, d.dep()));
        }
    }
};
