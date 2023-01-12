/*++
  Copyright (c) 2020 Arie Gurfinkel

  Module Name:

  spacer_expand_bnd_generalizer.cpp

  Abstract:

  Strengthen lemmas by changing numeral constants inside arithmetic literals

  Author:

  Hari Govind V K
  Arie Gurfinkel

--*/
#include "muz/spacer/spacer_expand_bnd_generalizer.h"
#include "ast/for_each_expr.h"
#include "ast/rewriter/expr_safe_replace.h"

namespace {
/// Returns true if \p e is arithmetic comparison
///
/// Returns true if \p e is of the form \p lhs op rhs, where
/// op in {<=, <, >, >=}, and rhs is a numeric value
bool is_arith_comp(const expr *e, expr *&lhs, rational &rhs, bool &is_int,
                   ast_manager &m) {
    arith_util arith(m);
    expr *e1, *e2;
    if (m.is_not(e, e1)) return is_arith_comp(e1, lhs, rhs, is_int, m);
    if (arith.is_le(e, lhs, e2) || arith.is_lt(e, lhs, e2) ||
        arith.is_ge(e, lhs, e2) || arith.is_gt(e, lhs, e2))
        return arith.is_numeral(e2, rhs, is_int);
    return false;
}

bool is_arith_comp(const expr *e, expr *&lhs, rational &rhs, ast_manager &m) {
    bool is_int;
    return is_arith_comp(e, lhs, rhs, is_int, m);
}
bool is_arith_comp(const expr *e, rational &rhs, ast_manager &m) {
    expr *lhs;
    return is_arith_comp(e, lhs, rhs, m);
}
/// If \p lit is of the form (x op v), replace v with num
///
/// Supports arithmetic literals where op is <, <=, >, >=, or negation
bool update_bound(const expr *lit, rational num, expr_ref &res,
                  bool negate = false) {
    SASSERT(is_app(lit));
    ast_manager &m = res.get_manager();
    expr *e1;
    if (m.is_not(lit, e1)) { return update_bound(e1, num, res, !negate); }

    arith_util arith(m);
    expr *lhs;
    rational val;
    bool is_int;
    if (!is_arith_comp(lit, lhs, val, is_int, m)) return false;

    res = m.mk_app(to_app(lit)->get_decl(), lhs, arith.mk_numeral(num, is_int));
    if (negate) { m.mk_not(res); }
    return true;
}

} // namespace
namespace spacer {

namespace collect_rationals_ns {

/// Finds rationals in an expression
struct proc {
    ast_manager &m;
    arith_util m_arith;

    vector<rational> &m_res;
    proc(ast_manager &a_m, vector<rational> &res)
        : m(a_m), m_arith(m), m_res(res) {}
    void operator()(expr *n) const {}
    void operator()(app *n) {
        rational val;
        if (m_arith.is_numeral(n, val)) m_res.push_back(val);
    }
};
} // namespace collect_rationals_ns

/// Extract all numerals from an expression
void collect_rationals(expr *e, vector<rational> &res, ast_manager &m) {
    collect_rationals_ns::proc proc(m, res);
    quick_for_each_expr(proc, e);
}

lemma_expand_bnd_generalizer::lemma_expand_bnd_generalizer(context &ctx)
    : lemma_generalizer(ctx), m(ctx.get_ast_manager()), m_arith(m) {
    // -- collect rationals from initial condition and transition relation
    for (auto &kv : ctx.get_pred_transformers()) {
        collect_rationals(kv.m_value->init(), m_values, m);
        collect_rationals(kv.m_value->transition(), m_values, m);
    }

    // remove duplicates
    std::sort(m_values.begin(), m_values.end());
    auto last = std::unique(m_values.begin(), m_values.end());
    for (size_t i = 0, sz = std::distance(last, m_values.end()); i < sz; ++i)
        m_values.pop_back();
}

void lemma_expand_bnd_generalizer::operator()(lemma_ref &lemma) {
    scoped_watch _w_(m_st.watch);
    if (!lemma->get_pob()->is_expand_bnd_enabled()) return;

    expr_ref_vector cube(lemma->get_cube());

    // -- temporary stores a core
    expr_ref_vector core(m);

    expr_ref lit(m), new_lit(m);
    rational bnd;
    // for every literal
    for (unsigned i = 0, sz = cube.size(); i < sz; i++) {
        lit = cube.get(i);
        if (m.is_true(lit)) continue;
        if (!is_arith_comp(lit, bnd, m)) continue;

        TRACE("expand_bnd", tout << "Attempting to expand " << lit << " inside "
                                 << cube << "\n";);

        // for every value
        for (rational n : m_values) {
            if (!is_interesting(lit, bnd, n)) continue;
            m_st.atmpts++;
            TRACE("expand_bnd", tout << "Attempting to expand " << lit
                                     << " with numeral " << n << "\n";);

            // -- update bound on lit
            VERIFY(update_bound(lit, n, new_lit));
            // -- update lit to new_lit for a new candidate lemma
            cube[i] = new_lit;

            core.reset();
            core.append(cube);
            // -- check that candidate is inductive
            if (check_inductive(lemma, core)) {
                expr_fast_mark1 in_core;
                for (auto *e : core) in_core.mark(e);
                for (unsigned i = 0, sz = cube.size(); i < sz; ++i) {
                    if (!in_core.is_marked(cube.get(i))) cube[i] = m.mk_true();
                }
                // move to next literal if the current has been removed
                if (!in_core.is_marked(new_lit)) break;
            } else {
                // -- candidate not inductive, restore original lit
                cube[i] = lit;
            }
        }
    }

    // Currently, we allow for only one round of expand bound per lemma
    // Mark lemma as already expanded so that it is not generalized in this way
    // again
    lemma->get_pob()->disable_expand_bnd_gen();
}

/// Check whether \p candidate is a possible generalization for \p lemma.
/// Side-effect: update \p lemma with the new candidate
bool lemma_expand_bnd_generalizer::check_inductive(lemma_ref &lemma,
                                                   expr_ref_vector &candidate) {
    TRACE("expand_bnd_verb",
          tout << "Attempting to update lemma with " << candidate << "\n";);

    unsigned uses_level = 0;
    auto &pt = lemma->get_pob()->pt();
    bool res = pt.check_inductive(lemma->level(), candidate, uses_level,
                                  lemma->weakness());
    if (res) {
        m_st.success++;
        lemma->update_cube(lemma->get_pob(), candidate);
        lemma->set_level(uses_level);
        TRACE("expand_bnd", tout << "expand_bnd succeeded with "
                                 << mk_and(candidate) << " at level "
                                 << uses_level << "\n";);
    }
    return res;
}

/// Check whether lit ==> lit[val |--> n] (barring special cases). That is,
/// whether \p lit becomes weaker if \p val is replaced with \p n
///
/// \p lit has to be of the form t <= v where v is a numeral.
/// Special cases:
/// In the trivial case in which \p val == \p n, return false.
/// if lit is an equality or the negation of an equality, return true.
bool lemma_expand_bnd_generalizer::is_interesting(const expr *lit, rational val,
                                                  rational new_val) {
    SASSERT(lit);
    // the only case in which negation and non negation agree
    if (val == new_val) return false;

    if (m.is_eq(lit)) return true;

    // negation is the actual negation modulo val == n
    expr *e1;
    if (m.is_not(lit, e1)) {
        return m.is_eq(lit) || !is_interesting(e1, val, new_val);
    }

    SASSERT(val != new_val);
    SASSERT(is_app(lit));

    if (to_app(lit)->get_family_id() != m_arith.get_family_id()) return false;
    switch (to_app(lit)->get_decl_kind()) {
    case OP_LE:
    case OP_LT:
        return new_val > val;
    case OP_GT:
    case OP_GE:
        return new_val < val;
    default:
        return false;
    }
}

void lemma_expand_bnd_generalizer::collect_statistics(statistics &st) const {
    st.update("time.spacer.solve.reach.gen.expand", m_st.watch.get_seconds());
    st.update("SPACER expand_bnd attmpts", m_st.atmpts);
    st.update("SPACER expand_bnd success", m_st.success);
}
} // namespace spacer
