/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_eq_approx.cpp

Abstract:

    Regular over-approximation of a word equation.

Author:

    Clemens Eisenhofer 2026

--*/

#include "ast/rewriter/seq_eq_approx.h"
#include "ast/ast_pp.h"

namespace {
    char const* mode_name(seq::transition_mode mode) {
        switch (mode) {
        case seq::transition_mode::brzozowski_tm: return "brzozowski";
        case seq::transition_mode::light_antimirov_tm: return "light-antimirov";
        }
        return "unknown";
    }

    char const* result_name(lbool r) {
        switch (r) {
        case l_true: return "consistent";
        case l_false: return "refuted";
        default: return "unknown";
        }
    }
}  // namespace

void seq_eq_approx::set_regex(expr* t, expr* regex) {
    m_h.insert(t, regex);
    m_h_pin.push_back(t);
    m_h_pin.push_back(regex);
}

void seq_eq_approx::unset_regex(expr* t) {
    m_h.remove(t);
}

void seq_eq_approx::reset_regexes() {
    m_h.reset();
    m_h_pin.reset();
}

expr* seq_eq_approx::get_regex(expr* t) const {
    expr* r = nullptr;
    m_h.find(t, r);
    return r;
}

bool seq_eq_approx::abstract_rec(expr* t, expr_ref_vector& parts, sort* re_sort) {
    expr* r = nullptr;
    if (m_h.find(t, r)) {
        if (r->get_sort() != re_sort)
            return false;
        parts.push_back(r);
        return true;
    }
    if (u().str.is_concat(t))
        return all_of(*to_app(t), [&](expr* arg) { return abstract_rec(arg, parts, re_sort); });
    if (u().str.is_empty(t))
        return true;
    zstring s;
    if (u().str.is_string(t, s)) {
        if (s.length() > 0)
            parts.push_back(re().mk_to_re(t));
        return true;
    }
    expr* elem = nullptr;
    if (u().str.is_unit(t, elem)) {
        if (m.is_value(elem))
            parts.push_back(re().mk_to_re(t));
        else
            parts.push_back(re().mk_full_char(re_sort));
        return true;
    }
    parts.push_back(re().mk_full_seq(re_sort));
    return true;
}

bool seq_eq_approx::abstract(expr* term, expr_ref& result) {
    sort* seq_sort = term->get_sort();
    if (!u().is_seq(seq_sort))
        return false;
    sort* re_sort = re().mk_re(seq_sort);
    expr_ref_vector parts(m);
    if (!abstract_rec(term, parts, re_sort))
        return false;
    if (parts.empty())
        result = re().mk_epsilon(seq_sort);
    else {
        result = parts.back();
        for (unsigned i = parts.size() - 1; i > 0; i--) {
            result = re().mk_concat(parts.get(i - 1), result);
        }
    }
    m_thrw(result, result);
    return true;
}

lbool seq_eq_approx::check(expr* lhs, expr* rhs) {
    ++m_stats.m_checks;
    m_last_result = l_undef;
    m_lhs_image = nullptr;
    m_rhs_image = nullptr;
    if (lhs->get_sort() != rhs->get_sort() || !u().is_seq(lhs->get_sort()) ||
        !abstract(lhs, m_lhs_image) || !abstract(rhs, m_rhs_image)) {
        ++m_stats.m_unsupported;
        return l_undef;
    }
    m_last_result = m_search.intersect_nonempty(m_lhs_image, m_rhs_image);
    if (m_last_result == l_undef)
        ++m_stats.m_giveup;
    return m_last_result;
}

lbool seq_eq_approx::check(expr* eq) {
    expr* lhs = nullptr, *rhs = nullptr;
    if (!m.is_eq(eq, lhs, rhs)) {
        ++m_stats.m_unsupported;
        return l_undef;
    }
    return check(lhs, rhs);
}

void seq_eq_approx::collect_statistics(::statistics& st) const {
    st.update("seq eq approx checks", m_stats.m_checks);
    st.update("seq eq approx unsupported", m_stats.m_unsupported);
    st.update("seq eq approx giveup", m_stats.m_giveup);
}

std::ostream& seq_eq_approx::display(std::ostream& out) const {
    auto display_expr = [&](expr* e) {
        if (e)
            out << mk_pp(e, m);
        else
            out << "null";
    };

    out << "(seq-eq-approx\n"
        << "  :mode " << mode_name(m_mode) << "\n"
        << "  :last-result " << result_name(m_last_result) << "\n"
        << "  :max-states " << max_states() << "\n"
        << "  :abstraction (";
    for (auto const& [t, r] : m_h) {
        out << "\n    ";
        display_expr(t);
        out << " -> ";
        display_expr(r);
    }
    if (!m_h.empty())
        out << "\n  ";
    out << ")\n  :lhs-image ";
    display_expr(m_lhs_image);
    out << "\n  :rhs-image ";
    display_expr(m_rhs_image);
    out << "\n  :checks " << m_stats.m_checks
        << "\n  :unsupported " << m_stats.m_unsupported
        << "\n  :giveup " << m_stats.m_giveup
        << ")\n";
    return out;
}
