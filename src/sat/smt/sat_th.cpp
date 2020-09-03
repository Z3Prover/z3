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
#include "tactic/tactic_exception.h"

namespace euf {

    bool th_internalizer::visit_rec(ast_manager& m, expr* a, bool sign, bool root, bool redundant) {
        IF_VERBOSE(110, verbose_stream() << "internalize: " << mk_pp(a, m) << "\n");
        flet<bool> _is_learned(m_is_redundant, redundant);
        sat::scoped_stack _sc(m_stack);
        unsigned sz = m_stack.size();
        visit(a);
        while (m_stack.size() > sz) {
        loop:
            if (!m.inc())
                throw tactic_exception(m.limit().get_cancel_msg());
            sat::eframe& fr = m_stack.back();
            expr* e = fr.m_e;
            if (visited(e)) {
                m_stack.pop_back();
                continue;
            }
            unsigned num = is_app(e) ? to_app(e)->get_num_args() : 0;

            while (fr.m_idx < num) {
                expr* arg = to_app(e)->get_arg(fr.m_idx);
                fr.m_idx++;
                if (!visit(arg))
                    goto loop;
            }
            if (!post_visit(e, sign, root && a == e))
                return false;
            m_stack.pop_back();
        }
        return true;
    }

    th_euf_solver::th_euf_solver(euf::solver& ctx, euf::theory_id id):
        th_solver(ctx.get_manager(), id),
        ctx(ctx)
    {}

    smt_params const& th_euf_solver::get_config() const {
        return ctx.get_config(); 
    }

    region& th_euf_solver::get_region() {
        return ctx.get_region();
    }

    enode* th_euf_solver::get_enode(expr* e) const { 
        return ctx.get_enode(e); 
    }

    sat::literal th_euf_solver::get_literal(expr* e) const {
        return ctx.get_literal(e);
    }

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
