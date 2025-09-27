#pragma once
#include "nlsat_types.h"

namespace nlsat {

    class assignment; // forward declared in nlsat_types.h

    class levelwise {
    public:
        struct indexed_root_expr {
            poly* p;
            unsigned i;
        };
        struct symbolic_interval {
            bool section = false;
            polynomial_ref l;
            unsigned l_index; // the root index
            polynomial_ref u;
            unsigned u_index; // the root index
            bool l_inf() const { return l == nullptr; }
            bool u_inf() const { return u == nullptr; }
            bool is_section() const { return section; }
            bool is_sector() const { return !section; }
            polynomial_ref& section_poly() {
                SASSERT(is_section());                
                return l;
            }
            symbolic_interval(polynomial::manager & pm):l(pm), u(pm) {}
        };
        // Free pretty-printer declared here so external modules (e.g., nlsat_explain) can
        // display intervals without depending on levelwise internals.
        // Implemented in levelwise.cpp
        friend std::ostream& display(std::ostream& out, solver& s, symbolic_interval const& I);
            
    private:


        struct impl;
        impl* m_impl;
    public:
    // Construct with polynomials ps, maximal variable max_x, current sample s, polynomial manager pm, and algebraic-number manager am
        levelwise(nlsat::solver& solver, polynomial_ref_vector const& ps, var max_x, assignment const& s, pmanager& pm, anum_manager& am);
        ~levelwise();

        levelwise(levelwise const&) = delete;
        levelwise& operator=(levelwise const&) = delete;
        std::vector<symbolic_interval> single_cell();        
    };

    //
    // Free pretty-printer (non-member) for levelwise::symbolic_interval
    std::ostream& display(std::ostream& out, solver& s, levelwise::symbolic_interval const& I);

} // namespace nlsat
