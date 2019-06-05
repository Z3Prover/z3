/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/
#pragma once
#include "math/lp/lp_settings.h"
namespace nla {
// forward definition
class solver;
}
namespace lp {
class lar_solver;
class lp_bound_propagator {
    std::unordered_map<unsigned, unsigned> m_improved_lower_bounds; // these maps map a column index to the corresponding index in ibounds
    std::unordered_map<unsigned, unsigned> m_improved_upper_bounds;
    lar_solver & m_lar_solver;
    nla::solver * m_nla_solver;
public:
    vector<implied_bound> m_ibounds;
public:
    lp_bound_propagator(lar_solver & ls, nla::solver * nla);
    column_type get_column_type(unsigned) const;

    bool lower_bound_is_available_for_column(unsigned) const;
    bool upper_bound_is_available_for_column(unsigned) const;
    bool lower_bound_is_available(unsigned) const;
    bool upper_bound_is_available(unsigned) const;
    impq get_lower_bound(unsigned) const;
    impq get_upper_bound(unsigned) const;
    void try_add_bound(mpq  v, unsigned j, bool is_low, bool coeff_before_j_is_pos, unsigned row_or_term_index, bool strict);
    virtual bool bound_is_interesting(unsigned vi,
                                      lp::lconstraint_kind kind,
                                      const rational & bval) {return true;}
    unsigned number_of_found_bounds() const { return m_ibounds.size(); }
    virtual void consume(mpq const& v, lp::constraint_index j) = 0;
};
}
