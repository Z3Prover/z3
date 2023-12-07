/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    polysat_model.cpp

Abstract:

    PolySAT model generation
    
Author:

    Nikolaj Bjorner (nbjorner) 2022-01-26

--*/

#include "params/bv_rewriter_params.hpp"
#include "sat/smt/polysat_solver.h"
#include "sat/smt/euf_solver.h"

namespace polysat {


    void solver::add_value(euf::enode* n, model& mdl, expr_ref_vector& values) {
#if 0
        auto p = expr2pdd(n->get_expr());
        rational val;
        VERIFY(m_polysat.try_eval(p, val));
        values[n->get_root_id()] = bv.mk_numeral(val, get_bv_size(n));    
#endif
    }   


    bool solver::check_model(sat::model const& m) const {
        return false;
    }

    void solver::finalize_model(model& mdl) {

    }

    std::ostream& solver::display_justification(std::ostream& out, sat::ext_justification_idx idx) const {
        return out;
    }

    std::ostream& solver::display_constraint(std::ostream& out, sat::ext_constraint_idx idx) const {
        return out;
    }

    std::ostream& solver::display(std::ostream& out) const {
        m_core.display(out);
        for (unsigned v = 0; v < get_num_vars(); ++v)
            if (m_var2pdd_valid.get(v, false))
                out << ctx.bpp(var2enode(v)) << " := " << m_var2pdd[v] << "\n";
        return out;
    }
}
