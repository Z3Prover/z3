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
            unsigned fsz = m_stack.size();
            expr* e = m_stack[fsz-1].m_e;
            if (visited(e)) {
                m_stack.pop_back();
                continue;
            }
            unsigned num = is_app(e) ? to_app(e)->get_num_args() : 0;

            while (m_stack[fsz - 1].m_idx < num) {
                expr* arg = to_app(e)->get_arg(m_stack[fsz - 1].m_idx);
                m_stack[fsz - 1].m_idx++;
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
        return ctx.expr2literal(e);
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
    
    void th_euf_solver::push_core() {
        m_var2enode_lim.push_back(m_var2enode.size());
    }

    void th_euf_solver::pop_core(unsigned num_scopes) {
        unsigned new_lvl = m_var2enode_lim.size() - num_scopes;
        m_var2enode.shrink(m_var2enode_lim[new_lvl]);
        m_var2enode_lim.shrink(new_lvl);
    }

    void th_euf_solver::pop(unsigned n) {
        unsigned k = std::min(m_num_scopes, n);
        m_num_scopes -= k;
        n -= k;
        if (n > 0)
            pop_core(n);        
    }

    bool th_euf_solver::add_unit(sat::literal lit) {
        return !is_true(lit) && (ctx.s().add_clause(1, &lit, sat::status::th(m_is_redundant, get_id())), true);
    }

    bool th_euf_solver::add_clause(sat::literal a, sat::literal b) {
        sat::literal lits[2] = { a, b };
        return !is_true(a, b) && (ctx.s().add_clause(2, lits, sat::status::th(m_is_redundant, get_id())), true);
    }

    bool th_euf_solver::add_clause(sat::literal a, sat::literal b, sat::literal c) {
        sat::literal lits[3] = { a, b, c };
        return !is_true(a, b, c) && (ctx.s().add_clause(3, lits, sat::status::th(m_is_redundant, get_id())), true);
    }

    bool th_euf_solver::add_clause(sat::literal a, sat::literal b, sat::literal c, sat::literal d) {
        sat::literal lits[4] = { a, b, c, d };
        return !is_true(a, b, c, d) && (ctx.s().add_clause(4, lits, sat::status::th(m_is_redundant, get_id())), true);
    }

    bool th_euf_solver::is_true(sat::literal lit) { 
        return ctx.s().value(lit) == l_true; 
    }

    euf::enode* th_euf_solver::mk_enode(expr* e, bool suppress_args) {
        m_args.reset();
        if (!suppress_args)
            for (expr* arg : *to_app(e))
                m_args.push_back(expr2enode(arg));
        euf::enode* n = ctx.mk_enode(e, m_args.size(), m_args.c_ptr());
        ctx.attach_node(n);
        return n;
    }

    void th_euf_solver::rewrite(expr_ref& a) {
        ctx.get_rewriter()(a);
    }

    expr_ref th_euf_solver::mk_eq(expr* e1, expr* e2) { 
        return ctx.mk_eq(e1, e2); 
    }

}
