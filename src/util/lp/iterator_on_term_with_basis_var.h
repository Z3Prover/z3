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
#include "util/lp/linear_combination_iterator.h"
#include "util/lp/numeric_pair.h"
#include "util/lp/lar_term.h"
namespace lp {
struct iterator_on_term_with_basis_var:linear_combination_iterator<mpq> {
    const lar_term & m_term;
    std::unordered_map<unsigned, mpq>::const_iterator m_i; // the offset in term coeffs
    bool             m_term_j_returned;
    unsigned         m_term_j;
    unsigned size() const override {return static_cast<unsigned>(m_term.m_coeffs.size() + 1);}
    iterator_on_term_with_basis_var(const lar_term & t, unsigned term_j) :
        m_term(t),
        m_i(t.m_coeffs.begin()),
        m_term_j_returned(false),
        m_term_j(term_j) {}

    bool next(mpq & a, unsigned & i) override {
        if (m_term_j_returned == false) {
            m_term_j_returned = true;
            a = - one_of_type<mpq>();
            i = m_term_j;
            return true;
        }
        if (m_i == m_term.m_coeffs.end())
            return false;
        i = m_i->first;
        a = m_i->second;
        m_i++;
        return true;
    }
    bool next(unsigned & i) override {
        if (m_term_j_returned == false) {
            m_term_j_returned = true;
            i = m_term_j;
            return true;
        }
        if (m_i == m_term.m_coeffs.end())
            return false;
        i = m_i->first;
        m_i++;
        return true;
    }
    void reset() override {
        m_term_j_returned = false;
        m_i = m_term.m_coeffs.begin();
    }
    linear_combination_iterator<mpq> * clone() override {
        iterator_on_term_with_basis_var * r = new iterator_on_term_with_basis_var(m_term, m_term_j);
        return r;
    }
};
}
