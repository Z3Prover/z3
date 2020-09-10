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

    trail_stack<euf::solver>& th_euf_solver::get_trail_stack() {
        return ctx.get_trail_stack();
    }

    enode* th_euf_solver::expr2enode(expr* e) const { 
        return ctx.get_enode(e); 
    }

    sat::literal th_euf_solver::expr2literal(expr* e) const {
        return ctx.get_literal(e);
    }

    expr* th_euf_solver::bool_var2expr(sat::bool_var v) const {
        return ctx.bool_var2expr(v);
    }

    theory_var th_euf_solver::mk_var(enode * n) {
        force_push();
        SASSERT(!is_attached_to_var(n));
        euf::theory_var v = m_var2enode.size();
        m_var2enode.push_back(n);
        return v;
    }

    bool th_euf_solver::is_attached_to_var(enode* n) const {
        theory_var v = n->get_th_var(get_id());
        return v != null_theory_var && var2enode(v) == n;
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

    unsigned th_euf_solver::lazy_pop(unsigned n) {
        if (n <= m_num_scopes) {
            m_num_scopes -= n;
            return 0;
        }
        else {
            n -= m_num_scopes;
            pop(n);
            return n;
        }
    }

    void th_euf_solver::add_unit(sat::literal lit) {
        ctx.s().add_clause(1, &lit, sat::status::th(m_is_redundant, get_id())); 
    }

    void th_euf_solver::add_clause(sat::literal a, sat::literal b) {
        sat::literal lits[2] = { a, b };
        ctx.s().add_clause(2, lits, sat::status::th(m_is_redundant, get_id()));
    }

    void th_euf_solver::add_clause(sat::literal a, sat::literal b, sat::literal c) {
        sat::literal lits[3] = { a, b, c };
        ctx.s().add_clause(3, lits, sat::status::th(m_is_redundant, get_id()));
    }

    void th_euf_solver::add_clause(sat::literal a, sat::literal b, sat::literal c, sat::literal d) {
        sat::literal lits[4] = { a, b, c, d };
        ctx.s().add_clause(4, lits, sat::status::th(m_is_redundant, get_id()));
    }

    euf::enode* th_euf_solver::mk_enode(expr* e, bool suppress_args) {
        m_args.reset();
        if (!suppress_args)
            for (expr* arg : *to_app(e))
                m_args.push_back(expr2enode(arg));
        euf::enode* n = ctx.mk_enode(e, m_args.size(), m_args.c_ptr());
        ctx.attach_node(n);
        if (m.is_bool(e)) {
            sat::bool_var v = ctx.get_si().add_bool_var(e);
            NOT_IMPLEMENTED_YET();
            // TODO: ctx.attach_lit(literal(v, false), e);
        }
        return n;
    }


    void th_euf_solver::rewrite(expr_ref& a) {
        ctx.get_rewriter()(a);
    }
}
