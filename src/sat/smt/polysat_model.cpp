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
        expr_ref value(m);
        if (n->interpreted())
            value = n->get_expr();
        else if (n->get_decl() && n->get_decl()->get_family_id() == bv.get_family_id()) {
            bv_rewriter rw(m);
            expr_ref_vector args(m);
            for (auto arg : euf::enode_args(n))
                args.push_back(values.get(arg->get_root_id()));
            rw.mk_app(n->get_decl(), args.size(), args.data(), value);
        }
        else {
            auto p = expr2pdd(n->get_expr());
            rational val;
            if (!m_core.try_eval(p, val)) {
                ctx.s().display(verbose_stream());
                verbose_stream() << ctx.bpp(n) << " := " << p << "\n";
                UNREACHABLE();
            }
            VERIFY(m_core.try_eval(p, val));
            value = bv.mk_numeral(val, get_bv_size(n));
        }
        values.set(n->get_root_id(), value);
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
        st.update("polysat-conflicts", m_stats.m_num_conflicts);
        st.update("polysat-axioms", m_stats.m_num_axioms);
        st.update("polysat-propagations", m_stats.m_num_propagations);            
    }

    std::ostream& solver::display_justification(std::ostream& out, sat::ext_justification_idx idx) const {
        return out;
    }

    std::ostream& solver::display_constraint(std::ostream& out, sat::ext_constraint_idx idx) const {
        return out;
    }

    std::ostream& solver::display(std::ostream& out) const {
        for (theory_var v = 0; v < get_num_vars(); ++v)
            if (m_var2pdd_valid.get(v, false))
                out << "tv" << v << " is " << ctx.bpp(var2enode(v)) << " := " << m_var2pdd[v] << "\n";
        m_core.display(out);
        m_intblast.display(out);
        return out;
    }

    void solver::validate_propagate(sat::literal lit, sat::literal_vector const& core, euf::enode_pair_vector const& eqs) {
        if (!ctx.get_config().m_core_validate)
            return;
        auto r = m_intblast.check_propagation(lit, core, eqs);
        VERIFY (r != l_true);
    }

    void solver::validate_conflict(sat::literal_vector const& core, euf::enode_pair_vector const& eqs) {
        if (!ctx.get_config().m_core_validate)
            return;
        auto r = m_intblast.check_core(core, eqs);
        VERIFY (r != l_true);
    }

    void solver::validate_axiom(sat::literal_vector const& clause) {
        if (!ctx.get_config().m_core_validate)
            return;
        auto r = m_intblast.check_axiom(clause);
        VERIFY (r != l_true);
    }

    std::ostream& solver::display_clause(char const* name, std::ostream& out, sat::literal_vector const& lits) const {
        out << name << ":\n";
        for (auto lit : lits)
            out << ctx.literal2expr(lit) << "\n";
        return out;
    }
}
