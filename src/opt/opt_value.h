/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    opt_value.h

Abstract:

    An optimization bound with an optional exact algebraic finite part.
    Values do not own models or certify optimality.

--*/
#pragma once

#include "ast/ast.h"
#include "util/inf_eps_rational.h"
#include "util/inf_rational.h"

namespace opt {

    typedef inf_eps_rational<inf_rational> inf_eps;

    class objective_value {
        inf_eps  m_bound;
        expr_ref m_exact;

    public:
        explicit objective_value(ast_manager& m, inf_eps const& bound = inf_eps()):
            m_bound(bound), m_exact(m) {}

        // Legacy search uses an outward rational endpoint, not the exact
        // finite part. Keep that choice explicit instead of converting implicitly.
        inf_eps const& rational_bound() const { return m_bound; }
        expr* exact_finite() const { return m_exact.get(); }
        bool is_finite() const { return m_bound.is_finite(); }
        bool has_infinitesimal() const { return !m_bound.get_infinitesimal().is_zero(); }

        objective_value& operator=(inf_eps const& bound) {
            m_bound = bound;
            m_exact = nullptr;
            return *this;
        }

        void reset() { *this = inf_eps(); }
        void reset_exact() { m_exact = nullptr; }
        void set_exact(inf_eps const& bound, expr* finite);
        void update_rational_bound(inf_eps const& bound);

        objective_value adjusted(rational const& offset, bool negate) const;
        expr_ref to_expr() const;
        void to_exprs(expr_ref_vector& es) const;

        // Equal isolating endpoints do not imply equal algebraic values.
        bool operator==(objective_value const& other) const;
        bool operator!=(objective_value const& other) const { return !(*this == other); }
    };
}
