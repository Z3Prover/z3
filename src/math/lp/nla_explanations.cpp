/*++
  Copyright (c) 2026 Microsoft Corporation

  Module Name:

  nla_explanations.cpp

  Author:
    Lev Nachmanson (levnach)

  --*/
#include "math/lp/nla_explanations.h"
#include "math/lp/nla_core.h"

namespace nla {

bool explanations::explain_upper_bound(const lp::lar_term& t, const rational& rs, lp::explanation& e) const {
    rational b(0); // the bound
    for (lp::lar_term::ival p : t) {
        rational pb;
        if (explain_coeff_upper_bound(p, pb, e)) {
            b += pb;
        } else {
            e.clear();
            return false;
        }
    }
    if (b > rs ) {
        e.clear();
        return false;
    }
    return true;
}

bool explanations::explain_lower_bound(const lp::lar_term& t, const rational& rs, lp::explanation& e) const {
    rational b(0); // the bound
    for (lp::lar_term::ival p : t) {
        rational pb;
        if (explain_coeff_lower_bound(p, pb, e)) {
            b += pb;
        } else {
            e.clear();
            return false;
        }
    }
    if (b < rs ) {
        e.clear();
        return false;
    }
    return true;
}

bool explanations::explain_coeff_lower_bound(const lp::lar_term::ival& p, rational& bound, lp::explanation& e) const {
    const rational& a = p.coeff();
    auto& lra = c().lra;
    SASSERT(!a.is_zero());
    if (a.is_pos()) {
        auto* dep = lra.get_column_lower_bound_witness(p.j());
        if (!dep)
            return false;
        bound = a * lra.get_lower_bound(p.j()).x;
        lra.push_explanation(dep, e);
        return true;
    }
    // a.is_neg()
    auto* dep = lra.get_column_upper_bound_witness(p.j());
    if (!dep)
        return false;
    bound = a * lra.get_upper_bound(p.j()).x;
    lra.push_explanation(dep, e);
    return true;
}

bool explanations::explain_coeff_upper_bound(const lp::lar_term::ival& p, rational& bound, lp::explanation& e) const {
    const rational& a = p.coeff();
    auto& lra = c().lra;
    lpvar j = p.j();
    SASSERT(!a.is_zero());
    if (a.is_neg()) {
        auto *dep = lra.get_column_lower_bound_witness(j);
        if (!dep)
            return false;
        bound = a * lra.get_lower_bound(j).x;
        lra.push_explanation(dep, e);
        return true;
    }
    // a.is_pos()
    auto* dep = lra.get_column_upper_bound_witness(j);
    if (!dep)
        return false;
    bound = a * lra.get_upper_bound(j).x;
    lra.push_explanation(dep, e);
    return true;
}

// return true iff the negation of the ineq can be derived from the constraints
bool explanations::explain_ineq(lemma_builder& lemma, const lp::lar_term& t, llc cmp, const rational& rs) {
    // check that we have something like 0 < 0, which is always false and can be safely
    // removed from the lemma

    if (t.is_empty() && rs.is_zero() &&
        (cmp == llc::LT || cmp == llc::GT || cmp == llc::NE)) return true;
    lp::explanation exp;
    bool r;
    switch (negate(cmp)) {
    case llc::LE:
        r = explain_upper_bound(t, rs, exp);
        break;
    case llc::LT:
        r = explain_upper_bound(t, rs - rational(1), exp);
        break;
    case llc::GE:
        r = explain_lower_bound(t, rs, exp);
        break;
    case llc::GT:
        r = explain_lower_bound(t, rs + rational(1), exp);
        break;

    case llc::EQ:
        r = (explain_lower_bound(t, rs, exp) && explain_upper_bound(t, rs, exp)) ||
            (rs.is_zero() && explain_by_equiv(t, exp));
        break;
    case llc::NE:
        // TBD - NB: does this work for Reals?
        r = explain_lower_bound(t, rs + rational(1), exp) || explain_upper_bound(t, rs - rational(1), exp);
        break;
    }
    if (r) {
        lemma &= exp;
        return true;
    }

    return false;
}

/**
 * \brief
 if t is an octagon term -+x -+ y try to explain why the term always is
 equal zero
*/
bool explanations::explain_by_equiv(const lp::lar_term& t, lp::explanation& e) const {
    lpvar i,j;
    bool sign;
    if (!is_octagon_term(t, sign, i, j))
        return false;
    auto& evars = c().m_evars;
    if (evars.find(signed_var(i, false)) != evars.find(signed_var(j, sign)))
        return false;

    evars.explain(signed_var(i, false), signed_var(j, sign), e);
    TRACE(nla_solver, tout << "explained :"; c().lra.print_term_as_indices(t, tout););
    return true;
}

// we look for octagon constraints here, with a left part  +-x +- y
void explanations::collect_equivs() {
    const lp::lar_solver& s = c().lra;

    for (const auto * t : s.terms()) {
        if (!s.column_associated_with_row(t->j()))
            continue;
        lpvar j = t->j();
        if (c().var_is_fixed_to_zero(j)) {
            TRACE(nla_solver_mons, s.print_term_as_indices(*t, tout << "term = ") << "\n";);
            add_equivalence_maybe(t, s.get_column_upper_bound_witness(j), s.get_column_lower_bound_witness(j));
        }
    }
    c().m_emons.ensure_canonized();
}

// returns true iff the term is in a form +-x-+y.
// the sign is true iff the term is x+y, -x-y.
bool explanations::is_octagon_term(const lp::lar_term& t, bool & sign, lpvar& i, lpvar &j) const {
    if (t.size() != 2)
        return false;
    bool seen_minus = false;
    bool seen_plus = false;
    i = null_lpvar;
    j = null_lpvar;
    for(lp::lar_term::ival p : t) {
        const auto & c = p.coeff();
        if (c == 1) {
            seen_plus = true;
        } else if (c == - 1) {
            seen_minus = true;
        } else {
            return false;
        }
        if (i == null_lpvar)
            i = p.j();
        else
            j = p.j();
    }
    SASSERT(j != null_lpvar);
    sign = (seen_minus && seen_plus)? false : true;
    return true;
}

void explanations::add_equivalence_maybe(const lp::lar_term* t, u_dependency* c0, u_dependency* c1) {
    bool sign;
    lpvar i, j;
    if (!is_octagon_term(*t, sign, i, j))
        return;
    if (sign)
        c().m_evars.merge_minus(i, j, eq_justification({c0, c1}));
    else
        c().m_evars.merge_plus(i, j, eq_justification({c0, c1}));
}

// x is equivalent to y if x = +- y
void explanations::init_vars_equivalence() {
    collect_equivs();
}

}
