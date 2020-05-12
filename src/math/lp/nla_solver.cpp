/*++
  Copyright (c) 2017 Microsoft Corporation

  Author:
    Lev Nachmanson (levnach)
    Nikolaj Bjorner (nbjorner)
  --*/
#include "math/lp/nla_solver.h"
#include <map>
#include "math/lp/monic.h"
#include "math/lp/lp_utils.h"
#include "math/lp/var_eqs.h"
#include "math/lp/factorization.h"
#include "math/lp/nla_solver.h"
namespace nla {

nla_settings& solver::settings() { return m_core->m_nla_settings; }

void solver::add_monic(lpvar v, unsigned sz, lpvar const* vs) {
    m_core->add_monic(v, sz, vs);
}

bool solver::is_monic_var(lpvar v) const {
    return m_core->is_monic_var(v);
}

bool solver::need_check() { return true; }

lbool solver::run_nra(lp::explanation & expl) {
    return m_nra.check(expl);
}


lbool solver::check(vector<lemma>& l, lp::explanation& expl) {    
    set_use_nra_model(false);
    lbool ret = m_core->check(l);
    if (ret == l_undef) { // disable the call to nlsat
        ret = run_nra(expl);
        if (ret == l_true || expl.size() > 0) {
            set_use_nra_model(true);
        }            
    }
    return ret;
}
 
void solver::push(){
    m_core->push();
}

void solver::pop(unsigned n) {
    m_core->pop(n);
}
        
solver::solver(lp::lar_solver& s): m_core(alloc(core, s, m_res_limit)),
                                   m_nra(s, m_res_limit, *m_core) {
}

bool solver::influences_nl_var(lpvar j) const {    
    return m_core->influences_nl_var(j);
}

solver::~solver() {
    dealloc(m_core);
}

std::ostream& solver::display(std::ostream& out) const {    
    m_core->print_monics(out);
    if( use_nra_model()) {
        return m_nra.display(out);
    }
    return out;
}

}
