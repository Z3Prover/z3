#pragma once
#include "nlsat_types.h"

namespace nlsat {

class assignment; // forward declared in nlsat_types.h

// Levelwise driver (PIMPL). Orchestrates property-based projection/proof.
class levelwise {
    struct impl;
    impl* m_impl;
public:
    // Construct with polynomials ps, maximal variable max_x, and current sample s (assignment of vars < max_x)
    levelwise(polynomial_ref_vector const& ps, var max_x, assignment const& s);
    ~levelwise();

    levelwise(levelwise const&) = delete;
    levelwise& operator=(levelwise const&) = delete;
    levelwise(levelwise&&) noexcept;
    levelwise& operator=(levelwise&&) noexcept;
};

// Convenience free-function driver prototype
void levelwise_project(polynomial_ref_vector const& ps, var max_x, assignment const& s);

} // namespace nlsat
