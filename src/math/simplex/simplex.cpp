/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    simplex.h

Abstract:

    Multi-precision simplex tableau.

Author:

    Nikolaj Bjorner (nbjorner) 2014-01-15

Notes:

--*/

#include "math/simplex/simplex.h"
#include "math/simplex/sparse_matrix_def.h"
#include "math/simplex/simplex_def.h"
#include "util/rational.h"
#include "util/inf_rational.h"

namespace simplex {
    template class simplex<mpz_ext>;
    template class simplex<mpq_ext>;

    static void refine_delta(rational& delta, inf_rational const& l, inf_rational const& u) {
        if (l.get_rational() < u.get_rational() && l.get_infinitesimal() > u.get_infinitesimal()) {
            rational new_delta = (u.get_rational() - l.get_rational()) / (l.get_infinitesimal() - u.get_infinitesimal());
            if (new_delta < delta) { 
                delta = new_delta;
            }
        }
    }


    void ensure_rational_solution(simplex<mpq_ext>& S) {
        rational delta(1);
        for (unsigned i = 0; i < S.get_num_vars(); ++i) {
            auto const& _value = S.get_value(i);
            inf_rational value(rational(_value.first), rational(_value.second));
            if (S.lower_valid(i)) {
                auto const& _bound = S.get_lower(i);
                inf_rational bound(rational(_bound.first), rational(_bound.second));
                refine_delta(delta, bound, value);
            }
            if (S.upper_valid(i)) {
                auto const& _bound = S.get_upper(i);
                inf_rational bound(rational(_bound.first), rational(_bound.second));
                refine_delta(delta, value, bound);
            }
        }
        unsynch_mpq_inf_manager inf_mgr;
        scoped_mpq_inf q(inf_mgr);
        for (unsigned i = 0; i < S.get_num_vars(); ++i) {
            auto const& _value = S.get_value(i);
            rational inf(_value.second);
            if (!inf.is_zero()) {
                rational fin = rational(_value.first) + inf * delta;
                inf = 0;
                inf_mgr.set(q, fin.to_mpq(), inf.to_mpq());
                S.set_value(i, q);
            }
        }
    }
};
