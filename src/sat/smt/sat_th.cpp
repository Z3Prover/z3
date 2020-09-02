/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    sat_th.cpp

Abstract:

    Theory plugin base classes

Author:

    Nikolaj Bjorner (nbjorner) 2020-08-25

--*/

#include "sat/smt/sat_th.h"
#include "sat/smt/euf_solver.h"

namespace euf {


    th_euf_solver::th_euf_solver(euf::solver& ctx, euf::theory_id id):
        th_solver(ctx.get_manager(), id),
        ctx(ctx)
    {}

    theory_var th_euf_solver::mk_var(enode * n) {
        SASSERT(!is_attached_to_var(n));
        euf::theory_var v = m_var2enode.size();
        m_var2enode.push_back(n);
        return v;
    }

    bool th_euf_solver::is_attached_to_var(enode* n) const {
        theory_var v = n->get_th_var(get_id());
        return v != null_theory_var && get_enode(v) == n;
    }

    theory_var th_euf_solver::get_th_var(expr* e) const {
        return get_th_var(ctx.get_enode(e));
    }
    
    void th_euf_solver::push() {
        m_var2enode_lim.push_back(m_var2enode.size());
    }

    void th_euf_solver::pop(unsigned num_scopes) {
        unsigned new_lvl = m_var2enode_lim.size() - num_scopes;
        m_var2enode.shrink(m_var2enode_lim[new_lvl]);
        m_var2enode_lim.shrink(new_lvl);
    }

}
