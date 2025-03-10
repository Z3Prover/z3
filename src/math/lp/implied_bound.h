/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    <name>

Abstract:

    <abstract>

Author:

    Lev Nachmanson (levnach)

Revision History:


--*/
#pragma once
#include "math/lp/lp_settings.h"
#include "math/lp/lar_constraints.h"
namespace lp {
class implied_bound {
    public:
    mpq m_bound;
    // It is either the column for which the bound has been found, or,
    // in the case the column was created as
    // the slack variable to a term, it is the term index.
    // It is the same index that was returned by lar_solver::add_var(), or
    // by lar_solver::add_term()
    unsigned m_j; 
    bool m_is_lower_bound;
    bool m_strict;
    private:
    std::function<u_dependency*()> m_explain_bound = nullptr;
    public:
    // s is expected to be the pointer to lp_bound_propagator.
    u_dependency* explain_implied() const { return m_explain_bound(); }
    void set_explain(std::function<u_dependency*()> f) { m_explain_bound = f; }
    lconstraint_kind kind() const {
        lconstraint_kind k = m_is_lower_bound? GE : LE;
        if (m_strict)
            k = static_cast<lconstraint_kind>(k / 2);
        return k;
    }
    implied_bound() = default;
    implied_bound(const mpq & a,
                  unsigned j,
                  bool is_lower_bound,
                  bool is_strict,
                  std::function<u_dependency*()> get_dep):
        m_bound(a),
        m_j(j),
        m_is_lower_bound(is_lower_bound),
        m_strict(is_strict),
        m_explain_bound(get_dep) {
    }
};
}
