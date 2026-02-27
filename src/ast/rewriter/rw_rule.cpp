/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    rw_rule.cpp

Abstract:

    Abstract machine for pattern-based term rewriting.  See rw_rule.h.

Author:

    Copilot 2026

Notes:

--*/

#include "ast/rewriter/rw_rule.h"
#include "ast/rewriter/rewriter_def.h"
#include "ast/arith_decl_plugin.h"
#include "ast/rewriter/var_subst.h"

// ---------------------------------------------------------------------------
// rw_table: internals
// ---------------------------------------------------------------------------

bool rw_table::match(expr * pattern, expr * term, ptr_vector<expr> & bindings) {
    if (is_var(pattern)) {
        unsigned idx = to_var(pattern)->get_idx();
        if (idx >= bindings.size())
            bindings.resize(idx + 1, nullptr);
        if (!bindings[idx])
            bindings[idx] = term;
        else if (bindings[idx] != term)
            return false;
        return true;
    }
    if (!is_app(pattern) || !is_app(term))
        return false;
    app * pat = to_app(pattern);
    app * trm = to_app(term);
    if (pat->get_decl() != trm->get_decl())
        return false;
    unsigned n = pat->get_num_args();
    if (n != trm->get_num_args())
        return false;
    for (unsigned i = 0; i < n; ++i)
        if (!match(pat->get_arg(i), trm->get_arg(i), bindings))
            return false;
    return true;
}

void rw_table::add_rule(unsigned num_vars, expr * lhs, expr * rhs) {
    SASSERT(is_app(lhs));
    func_decl * head = to_app(lhs)->get_decl();
    unsigned idx = m_rules.size();
    m_rules.push_back(alloc(rw_rule, m, num_vars, lhs, rhs));
    m_index.insert_if_not_there(head, unsigned_vector()).push_back(idx);
}

br_status rw_table::apply(func_decl * f, unsigned num, expr * const * args, expr_ref & result) {
    auto * entry = m_index.find_core(f);
    if (!entry)
        return BR_FAILED;
    unsigned_vector & rule_ids = entry->get_data().m_value;
    for (unsigned idx : rule_ids) {
        rw_rule * rule = m_rules[idx];
        app * lhs = to_app(rule->m_lhs.get());
        if (lhs->get_num_args() != num)
            continue;
        ptr_vector<expr> bindings;
        bindings.resize(rule->m_num_vars, nullptr);
        bool ok = true;
        for (unsigned i = 0; i < num && ok; ++i)
            ok = match(lhs->get_arg(i), args[i], bindings);
        if (ok) {
            // verify all declared variables were bound
            for (unsigned i = 0; i < rule->m_num_vars && ok; ++i)
                if (!bindings[i]) ok = false;
        }
        if (!ok)
            continue;
        var_subst subst(m, false); // VAR(i) -> bindings[i]
        result = subst(rule->m_rhs.get(), bindings.size(), bindings.data());
        return BR_DONE;
    }
    return BR_FAILED;
}

// ---------------------------------------------------------------------------
// populate_rules: representative simplification rules
// ---------------------------------------------------------------------------

void rw_table::populate_rules() {
    arith_util arith(m);

    sort * int_sort  = arith.mk_int();
    sort * real_sort = arith.mk_real();
    sort * bool_sort = m.mk_bool_sort();

    // constant numerals used in patterns
    expr_ref zero_i(arith.mk_int(0),  m);
    expr_ref one_i (arith.mk_int(1),  m);
    expr_ref zero_r(arith.mk_real(0), m);
    expr_ref one_r (arith.mk_real(1), m);

    expr_ref t_true (m.mk_true(),  m);
    expr_ref t_false(m.mk_false(), m);

    // pattern variables (VAR(i) with explicit sort)
    expr_ref v0i(m.mk_var(0, int_sort),  m);
    expr_ref v1i(m.mk_var(1, int_sort),  m);
    expr_ref v0r(m.mk_var(0, real_sort), m);
    expr_ref v1r(m.mk_var(1, real_sort), m);
    expr_ref v0b(m.mk_var(0, bool_sort), m);
    expr_ref v1b(m.mk_var(1, bool_sort), m);

    // ------------------------------------------------------------------
    // Arithmetic: addition identity  0 + x -> x  and  x + 0 -> x
    // ------------------------------------------------------------------
    add_rule(1, arith.mk_add(zero_i, v0i), v0i);  // 0_i + x -> x  (Int)
    add_rule(1, arith.mk_add(v0i, zero_i), v0i);  // x + 0_i -> x  (Int)
    add_rule(1, arith.mk_add(zero_r, v0r), v0r);  // 0_r + x -> x  (Real)
    add_rule(1, arith.mk_add(v0r, zero_r), v0r);  // x + 0_r -> x  (Real)

    // Arithmetic: multiplication identity  1 * x -> x  and  x * 1 -> x
    add_rule(1, arith.mk_mul(one_i, v0i), v0i);   // 1_i * x -> x  (Int)
    add_rule(1, arith.mk_mul(v0i, one_i), v0i);   // x * 1_i -> x  (Int)
    add_rule(1, arith.mk_mul(one_r, v0r), v0r);   // 1_r * x -> x  (Real)
    add_rule(1, arith.mk_mul(v0r, one_r), v0r);   // x * 1_r -> x  (Real)

    // Arithmetic: multiplication by zero  0 * x -> 0  and  x * 0 -> 0
    add_rule(1, arith.mk_mul(zero_i, v0i), zero_i); // 0_i * x -> 0  (Int)
    add_rule(1, arith.mk_mul(v0i, zero_i), zero_i); // x * 0_i -> 0  (Int)
    add_rule(1, arith.mk_mul(zero_r, v0r), zero_r); // 0_r * x -> 0  (Real)
    add_rule(1, arith.mk_mul(v0r, zero_r), zero_r); // x * 0_r -> 0  (Real)

    // Arithmetic: subtraction  x - 0 -> x
    add_rule(1, arith.mk_sub(v0i, zero_i), v0i);  // x - 0_i -> x  (Int)
    add_rule(1, arith.mk_sub(v0r, zero_r), v0r);  // x - 0_r -> x  (Real)

    // Arithmetic: unary minus double negation  -(-x) -> x
    add_rule(1, arith.mk_uminus(arith.mk_uminus(v0i)), v0i); // -(-x) -> x  (Int)
    add_rule(1, arith.mk_uminus(arith.mk_uminus(v0r)), v0r); // -(-x) -> x  (Real)

    // ------------------------------------------------------------------
    // Boolean: and/or identities and annihilators
    // ------------------------------------------------------------------
    add_rule(1, m.mk_and(t_true,  v0b), v0b);    // true  /\ x -> x
    add_rule(1, m.mk_and(v0b, t_true),  v0b);    // x /\ true  -> x
    add_rule(1, m.mk_and(t_false, v0b), t_false); // false /\ x -> false
    add_rule(1, m.mk_and(v0b, t_false), t_false); // x /\ false -> false

    add_rule(1, m.mk_or(t_false, v0b), v0b);     // false \/ x -> x
    add_rule(1, m.mk_or(v0b, t_false), v0b);     // x \/ false -> x
    add_rule(1, m.mk_or(t_true,  v0b), t_true);  // true  \/ x -> true
    add_rule(1, m.mk_or(v0b, t_true),  t_true);  // x \/ true  -> true

    // Boolean: double negation  not(not(x)) -> x
    add_rule(1, m.mk_not(m.mk_not(v0b)), v0b);

    // Boolean: negation of constants
    add_rule(0, m.mk_not(m.mk_true()),  m.mk_false()); // not(true)  -> false
    add_rule(0, m.mk_not(m.mk_false()), m.mk_true());  // not(false) -> true

    // ------------------------------------------------------------------
    // ITE simplifications (Bool, Int, Real branches)
    // ------------------------------------------------------------------
    // ite(true,  x, y) -> x
    add_rule(2, m.mk_ite(t_true,  v0b, v1b), v0b); // Bool
    add_rule(2, m.mk_ite(t_true,  v0i, v1i), v0i); // Int
    add_rule(2, m.mk_ite(t_true,  v0r, v1r), v0r); // Real

    // ite(false, x, y) -> y
    add_rule(2, m.mk_ite(t_false, v0b, v1b), v1b); // Bool
    add_rule(2, m.mk_ite(t_false, v0i, v1i), v1i); // Int
    add_rule(2, m.mk_ite(t_false, v0r, v1r), v1r); // Real

    // ite(c, x, x) -> x  (both branches identical, VAR(1) used twice)
    add_rule(2, m.mk_ite(v0b, v1b, v1b), v1b); // Bool
    add_rule(2, m.mk_ite(v0b, v1i, v1i), v1i); // Int
    add_rule(2, m.mk_ite(v0b, v1r, v1r), v1r); // Real

    // ------------------------------------------------------------------
    // Equality: x = x -> true
    // ------------------------------------------------------------------
    add_rule(1, m.mk_eq(v0b, v0b), t_true); // Bool
    add_rule(1, m.mk_eq(v0i, v0i), t_true); // Int
    add_rule(1, m.mk_eq(v0r, v0r), t_true); // Real
}

template class rewriter_tpl<rw_table>;
