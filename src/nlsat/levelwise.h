#pragma once
#include "nlsat_types.h"

namespace nlsat {

    class assignment; // forward declared in nlsat_types.h
    struct symbolic_interval {};

    class levelwise {
        struct impl;
        impl* m_impl;
    public:
        // Construct with polynomials ps, maximal variable max_x, and current sample s (assignment of vars < max_x)
        levelwise(polynomial_ref_vector const& ps, var max_x, assignment const& s);
        ~levelwise();

        levelwise(levelwise const&) = delete;
        levelwise& operator=(levelwise const&) = delete;
        std::vector<symbolic_interval> single_cell();        
    };

    //

} // namespace nlsat
