/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_membership_length_constraints.cpp

Abstract:

    Consistency checks for sequence membership constraints based on lengths.

--*/

#include "ast/rewriter/seq_membership_length_constraints.h"
#include "ast/rewriter/seq_rewriter.h"

namespace seq {

bool membership_length_constraints::is_var(expr* term) const {
    return m_is_var ? m_is_var(term) : is_uninterp(term);
}

bool membership_length_constraints::length_interval(expr* regex, unsigned& lo, unsigned& hi) const {
    auto& re = m_rw.u().re;
    expr* body = nullptr, *head = nullptr, *tail = nullptr;
    unsigned lower = 0, upper = 0;
    if (re.is_full_char(regex)) {
        lo = hi = 1;
        return true;
    }
    if (re.is_epsilon(regex)) {
        lo = hi = 0;
        return true;
    }
    if (re.is_loop(regex, body, lower, upper) && re.is_full_char(body)) {
        lo = lower;
        hi = upper;
        return true;
    }
    if (!re.is_concat(regex, head, tail) || !re.is_full_seq(tail))
        return false;
    if (re.is_full_char(head)) {
        lo = 1;
        hi = UINT_MAX;
        return true;
    }
    if (re.is_loop(head, body, lower, upper) && re.is_full_char(body) && lower == upper) {
        lo = lower;
        hi = UINT_MAX;
        return true;
    }
    return false;
}

lbool membership_length_constraints::check(constraint_vector const& constraints) {
    m_core.reset();
    obj_map<expr, unsigned> lo_bounds;
    obj_map<expr, void*> lo_dependencies;
    for (auto const& [term, regex, dependency] : constraints) {
        unsigned lo = 0, hi = 0, current = 0;
        if (length_interval(regex, lo, hi) && lo > 0 &&
            (!lo_bounds.find(term.get(), current) || lo > current)) {
            lo_bounds.insert(term.get(), lo);
            lo_dependencies.insert(term.get(), dependency);
        }
    }

    auto add_dependency = [&](void* dependency) {
        if (!dependency)
            return;
        for (void* existing : m_core)
            if (existing == dependency)
                return;
        m_core.push_back(dependency);
    };

    std::function<bool(expr*, unsigned&)> min_length = [&](expr* term, unsigned& result) {
        auto& str = m_rw.u().str;
        if (str.is_concat(term)) {
            result = 0;
            for (expr* arg : *to_app(term)) {
                unsigned arg_length = 0;
                if (!min_length(arg, arg_length))
                    return false;
                result = add_truncate(result, arg_length);
            }
            return true;
        }
        if (str.is_empty(term)) {
            result = 0;
            return true;
        }
        zstring value;
        if (str.is_string(term, value)) {
            result = value.length();
            return true;
        }
        expr* element = nullptr;
        if (str.is_unit(term, element) && m_rw.m().is_value(element)) {
            result = 1;
            return true;
        }
        if (!is_var(term))
            return false;
        result = 0;
        if (lo_bounds.find(term, result) && result > 0) {
            void* dependency = nullptr;
            if (lo_dependencies.find(term, dependency))
                add_dependency(dependency);
        }
        return true;
    };

    for (auto const& [term, regex, dependency] : constraints) {
        unsigned max_length = m_rw.u().re.max_length(regex);
        if (max_length == UINT_MAX)
            continue;
        m_core.reset();
        unsigned lower = 0;
        if (!min_length(term, lower) || lower <= max_length)
            continue;
        add_dependency(dependency);
        return l_false;
    }
    m_core.reset();
    return l_true;
}

}
