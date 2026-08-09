/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_membership_length_constraints.h

Abstract:

    Consistency checks for sequence membership constraints based on lengths.

--*/
#pragma once

#include "ast/ast.h"
#include "util/lbool.h"
#include "util/vector.h"
#include <functional>
#include <tuple>

class seq_rewriter;

namespace seq {

class membership_length_constraints {
public:
    using constraint = std::tuple<expr_ref, expr_ref, void*>;
    using constraint_vector = vector<constraint>;

private:
    seq_rewriter& m_rw;
    ptr_vector<void> m_core;
    std::function<bool(expr*)> m_is_var;

    bool is_var(expr* term) const;
    bool length_interval(expr* regex, unsigned& lo, unsigned& hi) const;

public:
    explicit membership_length_constraints(seq_rewriter& rw) : m_rw(rw) {}

    void set_is_var(std::function<bool(expr*)> const& is_var) { m_is_var = is_var; }

    // Return l_false when the constraints are inconsistent and populate core().
    // Return l_true when no contradiction was found.
    lbool check(constraint_vector const& constraints);

    ptr_vector<void> const& core() const { return m_core; }
};

}
