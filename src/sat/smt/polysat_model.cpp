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
#include "ast/rewriter/bv_rewriter.h"

namespace polysat {


    void solver::add_value(euf::enode* n, model& mdl, expr_ref_vector& values) {        
        auto p = expr2pdd(n->get_expr());
        rational val;
        if (!m_core.try_eval(p, val)) {
            ctx.s().display(verbose_stream());
            verbose_stream() << ctx.bpp(n) << " := " << p << "\n";
            UNREACHABLE();
        }
        VERIFY(m_core.try_eval(p, val));
        values.set(n->get_root_id(), bv.mk_numeral(val, get_bv_size(n)));
    }   

    bool solver::add_dep(euf::enode* n, top_sort<euf::enode>& dep) {
        if (!is_app(n->get_expr()))
            return false;
        app* e = to_app(n->get_expr());
        if (n->num_args() == 0) {
            dep.insert(n, nullptr);
            return true;
        }
        if (e->get_family_id() != bv.get_family_id())
            return false;
        for (euf::enode* arg : euf::enode_args(n))
            dep.add(n, arg->get_root());
        return true;
    }


    bool solver::check_model(sat::model const& m) const {
        return true;
    }

    void solver::finalize_model(model& mdl) {

    }

    void solver::collect_statistics(statistics& st) const {
        m_intblast.collect_statistics(st);
        m_core.collect_statistics(st);
    }

    std::ostream& solver::display_justification(std::ostream& out, sat::ext_justification_idx idx) const {
        return out;
    }

    std::ostream& solver::display_constraint(std::ostream& out, sat::ext_constraint_idx idx) const {
        return out;
    }

    std::ostream& solver::display(std::ostream& out) const {
        for (unsigned v = 0; v < get_num_vars(); ++v)
            if (m_var2pdd_valid.get(v, false))
                out << ctx.bpp(var2enode(v)) << " := " << m_var2pdd[v] << "\n";
        m_core.display(out);
        m_intblast.display(out);
        return out;
    }
}
