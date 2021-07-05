/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    set of viable values as wrap-around interval

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

Notes:

    
  replace BDDs by viable sets that emulate affine relations.
  viable_set has an interval of feasible values.
  it also can use ternary bit-vectors.
  or we could also just use a vector of lbool instead of ternary bit-vectors
  updating them at individual positions is relatively cheap instead of copying the
  vectors every time a range is narrowed.
    
    
--*/
#pragma once


#include <limits>

#include "math/dd/dd_bdd.h"
#include "math/polysat/types.h"
#include "math/interval/mod_interval.h"


namespace polysat {

  
    class viable_set : public mod_interval<rational> {
        unsigned m_num_bits;
        rational p2() const { return rational::power_of_two(m_num_bits); }
        bool is_max(rational const& a) const override;
        void intersect_eq(rational const& a, bool is_positive);
        bool narrow(std::function<bool(rational const&)>& eval);
    public:
        viable_set(unsigned num_bits): m_num_bits(num_bits) {}
        ~viable_set() override {}
        dd::find_t find_hint(rational const& c, rational& val) const;
        bool intersect_eq(rational const& a, rational const& b, bool is_positive);
        bool intersect_le(rational const& a, rational const& b, rational const& c, rational const& d, bool is_positive);
        rational prev(rational const& p) const;
	    rational next(rational const& p) const;
    };

}


