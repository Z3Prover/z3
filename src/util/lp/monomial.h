/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    <name>

Abstract:

    <abstract>

Author:
    Nikolaj Bjorner (nbjorner)
    Lev Nachmanson (levnach)

Revision History:


--*/
#pragma once
namespace lp {
struct monomial {
    mpq           m_coeff; // the coefficient of the monomial
    var_index     m_var; // the variable index
public:
    monomial(const mpq& coeff, var_index var) : m_coeff(coeff), m_var(var) {}
    monomial(var_index var) : monomial(one_of_type<mpq>(), var) {}
    const mpq & coeff() const { return m_coeff; }
    mpq & coeff() { return m_coeff; }
    var_index var() const { return m_var; }
    std::pair<mpq, var_index> to_pair() const { return std::make_pair(coeff(), var());}
};
}
