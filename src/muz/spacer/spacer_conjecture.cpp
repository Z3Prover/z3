/**
   Copyright (c) 2019 Microsoft Corporation and Arie Gurfinkel

   Module Name:

   spacer_conjecture.cpp

   Abstract:

   Methods to implement conjecture rule in gspacer

   Author:

   Arie Gurfinkel
   Hari Govind


   Notes:

--*/

#include "ast/for_each_expr.h"

#include "muz/spacer/spacer_context.h"
#include "muz/spacer/spacer_util.h"

namespace spacer {
/// Returns true if \p lit is LA/BV inequality with a single free variable
bool is_mono_var_lit(expr *lit, ast_manager &m) {
    expr *e;
    bv_util bv(m);
    arith_util a_util(m);
    if (m.is_not(lit, e)) return is_mono_var_lit(e, m);
    if (a_util.is_arith_expr(lit) || bv.is_bv_ule(lit) ||
        bv.is_bv_sle(lit)) {
        return get_num_vars(lit) == 1 && !has_nonlinear_var_mul(lit, m);
    }
    return false;
}

/// Returns true if \p pattern contains a single mono-var literal
///
/// That is, \p pattern contains a single suitable literal.
/// The literal is returned in \p res
bool find_unique_mono_var_lit(const expr_ref &pattern, expr_ref &res) {
    if (get_num_vars(pattern) != 1) return false;
    ast_manager &m = res.m();

    // if the pattern has multiple literals, check whether exactly one of them
    // is leq
    expr_ref_vector conj(m);
    conj.push_back(pattern);
    flatten_and(conj);
    unsigned count = 0;
    for (auto *lit : conj) {
        if (is_mono_var_lit(lit, m)) {
            if (count) return false;
            res = lit;
            count++;
        }
    }
    SASSERT(count <= 1);
    return count == 1;
}

/// Filter out a given literal \p lit from a list of literals
///
/// Returns true if at least one literal was filtered out
/// \p out contains all the remaining (not filtered) literals
/// \p out holds the result. Returns true if any literal has been dropped
bool filter_out_lit(const expr_ref_vector &vec, const expr_ref &lit, expr_ref_vector &out) {
    ast_manager &m = vec.get_manager();
    bool dirty = false, pos = false;
    sem_matcher matcher(m);
    substitution sub(m);

    out.reset();
    unsigned lit_num_vars = get_num_vars(lit.get());
    SASSERT(!(m.is_not(lit) && m.is_eq(to_app(lit)->get_arg(0))));
    for (auto &c : vec) {
        sub.reset();
        sub.reserve(1, lit_num_vars);
        matcher.reset();

        if (matcher(lit, c, sub, pos) && pos) {
            if (is_numeric_sub(sub)) {
                dirty = true;
                continue;
            }
        }
        out.push_back(c);
    }

    CTRACE("global", dirty,
           tout << "Filtered " << lit << " from " << vec << "\n got " << out << "\n";);
    return dirty;
}
} // namespace spacer
