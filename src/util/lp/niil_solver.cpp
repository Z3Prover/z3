/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    <name>

Abstract:

    <abstract>

Author:
    Nikolaj Bjorner (nbjorner)
    Lev Nachmanson (levnach)

Revision History:


--*/
#include "util/lp/niil_solver.h"
#include "util/map.h"
namespace niil {
struct solver::imp {
    imp(lp::lar_solver& s, reslimit& lim, params_ref const& p)
    // :
        // s(s), 
        // m_limit(lim),
        // m_params(p)
    {
    }
};
void solver::add_monomial(lp::var_index v, unsigned sz, lp::var_index const* vs) {
    std::cout << "called add_monomial\n";
}
solver::solver(lp::lar_solver& s, reslimit& lim, params_ref const& p) {
    m_imp = alloc(imp, s, lim, p);
}


}
