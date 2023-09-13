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
    unsigned m_j; // the column for which the bound has been found
    bool m_is_lower_bound;
	bool m_strict;
    private:
    std::function<u_dependency*(void)> m_explain_bound = nullptr;
    public:
    u_dependency* explain() const { return m_explain_bound(); }
    void set_explain(std::function<u_dependency*(void)> f) { m_explain_bound = f; }
    lconstraint_kind kind() const {
        lconstraint_kind k = m_is_lower_bound? GE : LE;
        if (m_strict)
            k = static_cast<lconstraint_kind>(k / 2);
        return k;
    }
    implied_bound(){}
    implied_bound(const mpq & a,
                  unsigned j,
                  bool is_lower_bound,
				  bool is_strict,
                  std::function<u_dependency*(void)> get_dep):
        m_bound(a),
        m_j(j),
        m_is_lower_bound(is_lower_bound),
        m_strict(is_strict),
        m_explain_bound(get_dep) {
    }
};
}
