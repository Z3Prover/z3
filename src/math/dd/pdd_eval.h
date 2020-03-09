/*++
Copyright (c) 2019 Microsoft Corporation

Module Name:

    dd_pdd.cpp

Abstract:

    Poly DD package 

Author:

    Nikolaj Bjorner (nbjorner) 2019-12-23
    Lev Nachmanson (levnach) 2019-12-23

Revision History:

--*/
#include "math/dd/dd_pdd.h"

namespace dd {
// calculates the value of a pdd expression based on the given values of the variables
class pdd_eval {
    
    std::function<rational (unsigned)> m_var2val;
    
public:
    
    pdd_eval() {}
    
    std::function<rational (unsigned)>& var2val() { return m_var2val; } // setter
    const std::function<rational (unsigned)>& var2val() const { return m_var2val; } // getter
    
    rational operator()(pdd const& p) {
        if (p.is_val()) {
            return p.val();
        }
        return (*this)(p.hi()) * m_var2val(p.var()) + (*this)(p.lo());
    }
};
}
