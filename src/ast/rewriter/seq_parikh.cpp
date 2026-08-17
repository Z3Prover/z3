/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_parikh.cpp

Abstract:

    Parikh-image filter over string equations and regex memberships.
    See seq_parikh.h.

TODOs:
- use the recorded memberships: they bound the Parikh image of their subject,
  which also refutes equations whose opaque tokens do not cancel.
- encode several equations at once instead of filtering them one at a time.
- cancel opaque tokens up to more than term identity (slices of a common base).
- finer cores once more than one constraint takes part in a refutation.

--*/

#include "ast/rewriter/seq_parikh.h"
#include "ast/ast_pp.h"

namespace {
    void add_count(obj_map<expr, int>& counts, expr* k, int d) {
        int c = 0;
        counts.find(k, c);
        counts.insert(k, c + d);
    }

    bool all_zero(obj_map<expr, int> const& counts) {
        for (auto const& kv : counts) {
            if (kv.m_value != 0)
                return false;
        }
        return true;
    }
}

void seq_parikh::count_tokens(expr* t, int sign, obj_map<expr, int>& elems, obj_map<expr, int>& opaque) {
    if (u().str.is_concat(t)) {
        for (expr* arg : *to_app(t)) {
            count_tokens(arg, sign, elems, opaque);
        }
        return;
    }
    if (u().str.is_empty(t))
        return;
    zstring s;
    if (u().str.is_string(t, s)) {
        for (unsigned i = 0; i < s.length(); ++i) {
            expr* elem = u().str.mk_char(s, i);
            m_pin.push_back(elem);
            add_count(elems, elem, sign);
        }
        return;
    }
    expr* elem = nullptr;
    if (u().str.is_unit(t, elem) && m.is_value(elem))
        add_count(elems, elem, sign);
    else
        add_count(opaque, t, sign);
}

lbool seq_parikh::check_eq(expr* lhs, expr* rhs) {
    obj_map<expr, int> elems, opaque;
    count_tokens(lhs, 1, elems, opaque);
    count_tokens(rhs, -1, elems, opaque);
    if (!all_zero(opaque)) {
        ++m_stats.m_eqs_skipped;
        return l_undef;
    }
    ++m_stats.m_eqs_checked;
    if (all_zero(elems))
        return l_undef;
    ++m_stats.m_conflicts;
    return l_false;
}

void seq_parikh::add_eq(expr* lhs, expr* rhs, void* d) {
    m_eqs.push_back({ expr_ref(lhs, m), expr_ref(rhs, m), d });
    m_undo_trail.push(push_back_vector(m_eqs));
}

void seq_parikh::add_mem(expr* term, expr* regex, void* d) {
    m_mems.push_back({ expr_ref(term, m), expr_ref(regex, m), d });
    m_undo_trail.push(push_back_vector(m_mems));
}

lbool seq_parikh::check() {
    m_core.reset();
    m_pin.reset();
    for (auto const& [lhs, rhs, d] : m_eqs) {
        if (check_eq(lhs, rhs) != l_false)
            continue;
        if (d)
            m_core.push_back(d);
        m_last_result = l_false;
        return m_last_result;
    }
    m_last_result = l_undef;
    return m_last_result;
}

std::ostream& seq_parikh::display(std::ostream& out) const {
    out << "(seq-parikh :last-result " << m_last_result << "\n";
    for (auto const& [lhs, rhs, d] : m_eqs) {
        out << "  (= " << mk_pp(lhs, m) << " " << mk_pp(rhs, m) << ")\n";
    }
    for (auto const& [term, regex, d] : m_mems) {
        out << "  (in " << mk_pp(term, m) << " " << mk_pp(regex, m) << ")\n";
    }
    return out << "  (:checked " << m_stats.m_eqs_checked
               << " :skipped " << m_stats.m_eqs_skipped
               << " :conflicts " << m_stats.m_conflicts << "))\n";
}

void seq_parikh::collect_statistics(::statistics& st) const {
    st.update("seq parikh equations checked", m_stats.m_eqs_checked);
    st.update("seq parikh equations skipped", m_stats.m_eqs_skipped);
    st.update("seq parikh conflicts", m_stats.m_conflicts);
}
