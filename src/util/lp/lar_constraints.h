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
#include "util/vector.h"
#include <utility>
#include <unordered_map>
#include <string>
#include <algorithm>
#include "util/lp/lp_utils.h"
#include "util/lp/ul_pair.h"
#include "util/lp/lar_term.h"
namespace lp {
inline lconstraint_kind flip_kind(lconstraint_kind t) {
    return static_cast<lconstraint_kind>( - static_cast<int>(t));
}

inline std::string lconstraint_kind_string(lconstraint_kind t) {
    switch (t) {
    case LE: return std::string("<=");
    case LT: return std::string("<");
    case GE: return std::string(">=");
    case GT: return std::string(">");
    case EQ: return std::string("=");
    }
    lp_unreachable();
    return std::string(); // it is unreachable
}

struct lar_base_constraint {
    lconstraint_kind m_kind;
    mpq m_right_side;
    virtual vector<std::pair<mpq, var_index>> get_left_side_coefficients() const = 0;
    lar_base_constraint() {}
    lar_base_constraint(lconstraint_kind kind, const mpq& right_side) :m_kind(kind), m_right_side(right_side) {}

    virtual unsigned size() const = 0;
    virtual ~lar_base_constraint(){}
    virtual mpq get_free_coeff_of_left_side() const { return zero_of_type<mpq>();}
};

struct lar_var_constraint: public lar_base_constraint {
    unsigned m_j;
    vector<std::pair<mpq, var_index>> get_left_side_coefficients() const override {
        vector<std::pair<mpq, var_index>> ret;
        ret.push_back(std::make_pair(one_of_type<mpq>(), m_j));
        return ret;
    }
    unsigned size() const override { return 1;}
    lar_var_constraint(unsigned j, lconstraint_kind kind, const mpq& right_side) : lar_base_constraint(kind, right_side), m_j(j) { }
};


struct lar_term_constraint: public lar_base_constraint {
    const lar_term * m_term;
    vector<std::pair<mpq, var_index>> get_left_side_coefficients() const override {
        return m_term->coeffs_as_vector();
    }
    unsigned size() const override { return m_term->size();}
    lar_term_constraint(const lar_term *t, lconstraint_kind kind, const mpq& right_side) : lar_base_constraint(kind, right_side), m_term(t) { }
    mpq get_free_coeff_of_left_side() const override { return m_term->m_v;}

};


class lar_constraint : public lar_base_constraint {
public:
    vector<std::pair<mpq, var_index>> m_coeffs;
    lar_constraint(const vector<std::pair<mpq, var_index>> & left_side, lconstraint_kind kind, const mpq & right_side)
        :  lar_base_constraint(kind, right_side), m_coeffs(left_side) {}
    
    lar_constraint(const lar_base_constraint & c) {
        lp_assert(false); // should not be called : todo!
    }

    unsigned size() const override {
        return static_cast<unsigned>(m_coeffs.size());
    }

    vector<std::pair<mpq, var_index>> get_left_side_coefficients() const override { return m_coeffs; }
};
}
