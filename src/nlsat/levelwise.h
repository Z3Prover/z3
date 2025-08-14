#pragma once
#include "nlsat_types.h"

namespace nlsat {

    class assignment; // forward declared in nlsat_types.h

    class levelwise {
    public:
        struct indexed_root_expr {
            poly* p;
            short i;
        };
        struct symbolic_interval {
            bool section = true;
            poly* l = nullptr;
            short l_index; // the root index
            poly* u = nullptr;
            short u_index; // the root index
            bool l_inf() const { return l == nullptr; }
            bool u_inf() const { return u == nullptr; }
            bool is_section() { return section; }
            bool is_sector() { return !section; }
            poly* section_poly() {
                SASSERT(is_section());                
                return l;
            }
        };
            
    private:


        struct impl;
        impl* m_impl;
    public:
    // Construct with polynomials ps, maximal variable max_x, current sample s, polynomial manager pm, and algebraic-number manager am
    levelwise(polynomial_ref_vector const& ps, var max_x, assignment const& s, pmanager& pm, anum_manager& am);
        ~levelwise();

        levelwise(levelwise const&) = delete;
        levelwise& operator=(levelwise const&) = delete;
        std::vector<symbolic_interval> single_cell();        
    };

    //

} // namespace nlsat
