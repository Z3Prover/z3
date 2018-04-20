/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Nikolaj Bjorner, Lev Nachmanson
*/
#include "util/lp/chase_cut_solver.h"
namespace lp {
    mpq polynomial::m_local_zero = zero_of_type<mpq>();

    size_t constraint_hash::operator() (const constraint* c) const { return c->id(); }
    
    bool constraint_equal::operator() (const constraint* a, const constraint * b) const { return a->id() == b->id(); }

    std::ostream& operator<<(std::ostream& out, pp_poly const& p) {
        p.s.print_polynomial(out, p.p);
        return out;
    }

    std::ostream& operator<<(std::ostream& out, pp_constraint const& c) {
        c.s.print_constraint(out, c.c);
        return out;
    }
}

