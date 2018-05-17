/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    <name>

Abstract:

    <abstract>

Author:
    Lev Nachmanson (levnach)
    Nikolaj Bjorner (nbjorner)

Revision History:


--*/
#pragma once
#include "util/lp/lar_term.h"
#include "util/lp/hnf.h"
#include "util/lp/general_matrix.h"
#include "util/lp/var_register.h"
namespace lp  {
class hnf_cutter {
    var_register m_var_register;
    general_matrix m_A;
    vector<const lar_term*> m_terms;
public:
    void clear() {
        m_A.clear();
        m_var_register.clear();
        m_terms.clear();
    }
    void add_term_to_A_for_hnf(const lar_term* t, const mpq &) {
        m_terms.push_back(t);
        for (const auto &p : *t) {
            m_var_register.register_user_var(p.var());
        }
    }
    void print(std::ostream & out) {
        out << "terms = " << m_terms.size() << ", var = " << m_var_register.size() << std::endl;
    }
};
}
