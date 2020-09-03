/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    euf_internalize.cpp

Abstract:

    Internalize utilities for EUF solver plugin.

Author:

    Nikolaj Bjorner (nbjorner) 2020-08-25

--*/

#include "ast/ast_pp.h"
#include "ast/pb_decl_plugin.h"
#include "sat/smt/euf_solver.h"

namespace euf {

    sat::literal solver::internalize(expr* e, bool sign, bool root, bool redundant) {
        if (si.is_bool_op(e))
            return si.internalize(e, redundant);
        auto* ext = get_solver(e);
        if (ext)
            return ext->internalize(e, sign, root, redundant);

        if (!visit_rec(m, e, sign, root, redundant))
            return sat::null_literal;
        SASSERT(m_egraph.find(e));
        return literal(m_expr2var.to_bool_var(e), sign);
    }

    bool solver::visit(expr* e) {
        euf::enode* n = m_egraph.find(e);
        if (n)
            return true;
        if (si.is_bool_op(e)) {
            sat::literal lit = si.internalize(e, m_is_redundant);
            n = m_var2node.get(lit.var(), nullptr);
            if (n && !lit.sign())
                return n;
            
            n = m_egraph.mk(e, 0, nullptr);
            attach_lit(lit, n);
            if (!m.is_true(e) && !m.is_false(e)) 
                s().set_external(lit.var());
            return true;
        }
        if (is_app(e) && to_app(e)->get_num_args() > 0) {
            m_stack.push_back(sat::eframe(e));
            return false;
        }
        n = m_egraph.mk(e, 0, nullptr);
        attach_node(n);
        return true;
    }

    bool solver::post_visit(expr* e, bool sign, bool root) {
        unsigned num = is_app(e) ? to_app(e)->get_num_args() : 0;
        m_args.reset();
        for (unsigned i = 0; i < num; ++i)
            m_args.push_back(m_egraph.find(to_app(e)->get_arg(i)));
        if (root && internalize_root(to_app(e), sign))
            return false;
        enode* n = m_egraph.mk(e, num, m_args.c_ptr());
        attach_node(n);
        return true;
    }

    bool solver::visited(expr* e) {
        return m_egraph.find(e) != nullptr;
    }

    void solver::attach_node(euf::enode* n) {
        expr* e = n->get_owner();
        log_node(n);
        if (m.is_bool(e)) {
            sat::bool_var v = si.add_bool_var(e);
            log_bool_var(v, n);
            attach_lit(literal(v, false),  n);
        }
        axiomatize_basic(n);
    }

    void solver::attach_lit(literal lit, euf::enode* n) {
        if (lit.sign()) {
            sat::bool_var v = si.add_bool_var(n->get_owner());
            sat::literal lit2 = literal(v, false);
            s().mk_clause(~lit, lit2, sat::status::th(false, m.get_basic_family_id()));
            s().mk_clause(lit, ~lit2, sat::status::th(false, m.get_basic_family_id()));
            lit = lit2;
        }
        sat::bool_var v = lit.var();
        m_var2node.reserve(v + 1, nullptr);
        SASSERT(m_var2node[v] == nullptr);
        m_var2node[v] = n;
        m_var_trail.push_back(v);
    }

    bool solver::internalize_root(app* e, bool sign) {
        if (m.is_distinct(e)) {
            enode_vector _args(m_args);
            if (sign)
                add_not_distinct_axiom(e, _args.c_ptr());
            else
                add_distinct_axiom(e, _args.c_ptr());
            return true;
        }
        return false;
    }

    void solver::add_not_distinct_axiom(app* e, enode* const* args) {
        SASSERT(m.is_distinct(e));
        unsigned sz = e->get_num_args();
        if (sz <= 1)
            return;

        sat::status st = sat::status::th(m_is_redundant, m.get_basic_family_id());
        static const unsigned distinct_max_args = 32;
        if (sz <= distinct_max_args) {
            sat::literal_vector lits;
            for (unsigned i = 0; i < sz; ++i) {
                for (unsigned j = i + 1; j < sz; ++j) {
                    expr_ref eq(m.mk_eq(args[i]->get_owner(), args[j]->get_owner()), m);
                    sat::literal lit = internalize(eq, false, false, m_is_redundant);
                    lits.push_back(lit);
                }
            }
            s().mk_clause(lits, st);
        }
        else {
            // g(f(x_i)) = x_i
            // f(x_1) = a + .... + f(x_n) = a >= 2
            sort* srt = m.get_sort(e->get_arg(0));
            SASSERT(!m.is_bool(srt));
            sort_ref u(m.mk_fresh_sort("distinct-elems"), m);
            sort* u_ptr = u.get();
            func_decl_ref f(m.mk_fresh_func_decl("dist-f", "", 1, &srt, u), m);
            func_decl_ref g(m.mk_fresh_func_decl("dist-g", "", 1, &u_ptr, srt), m);
            expr_ref a(m.mk_fresh_const("a", u), m);
            expr_ref_vector eqs(m);
            for (expr* arg : *e) {
                expr_ref fapp(m.mk_app(f, arg), m);
                expr_ref gapp(m.mk_app(g, fapp.get()), m);
                expr_ref eq(m.mk_eq(gapp, arg), m);
                sat::literal lit = internalize(eq, false, false, m_is_redundant);
                s().add_clause(1, &lit, st);
                eqs.push_back(m.mk_eq(fapp, a));
            }
            pb_util pb(m);
            expr_ref at_least2(pb.mk_at_least_k(eqs.size(), eqs.c_ptr(), 2), m);
            sat::literal lit = si.internalize(at_least2, m_is_redundant);
            s().mk_clause(1, &lit, st);
        }
    }

    void solver::add_distinct_axiom(app* e, enode* const* args) {
        SASSERT(m.is_distinct(e));
        static const unsigned distinct_max_args = 32;
        unsigned sz = e->get_num_args();
        sat::status st = sat::status::th(m_is_redundant, m.get_basic_family_id());
        if (sz <= 1) {
            s().mk_clause(0, nullptr, st);
            return;
        }           
        if (sz <= distinct_max_args) {
            for (unsigned i = 0; i < sz; ++i) {
                for (unsigned j = i + 1; j < sz; ++j) {
                    expr_ref eq(m.mk_eq(args[i]->get_owner(), args[j]->get_owner()), m);
                    sat::literal lit = internalize(eq, true, false, m_is_redundant);
                    s().add_clause(1, &lit, st);
                }
            }
        }
        else {
            // dist-f(x_1) = v_1 & ... & dist-f(x_n) = v_n
            sort* srt = m.get_sort(e->get_arg(0));
            SASSERT(!m.is_bool(srt));
            sort_ref u(m.mk_fresh_sort("distinct-elems"), m);
            func_decl_ref f(m.mk_fresh_func_decl("dist-f", "", 1, &srt, u), m);
            for (unsigned i = 0; i < sz; ++i) {
                expr_ref fapp(m.mk_app(f, e->get_arg(i)), m);
                expr_ref fresh(m.mk_fresh_const("dist-value", u), m);
                enode* n = m_egraph.mk(fresh, 0, nullptr);
                n->mark_interpreted();
                expr_ref eq(m.mk_eq(fapp, fresh), m);
                sat::literal lit = internalize(eq, false, false, m_is_redundant);
                s().add_clause(1, &lit, st);
            }
        }
    }

    void solver::axiomatize_basic(enode* n) {
        expr* e = n->get_owner();
        sat::status st = sat::status::th(m_is_redundant, m.get_basic_family_id());
        if (m.is_ite(e)) {        
            app* a = to_app(e);
            expr* c = a->get_arg(0);
            expr* th = a->get_arg(1);
            expr* el = a->get_arg(2);
            sat::bool_var v = m_expr2var.to_bool_var(c);
            SASSERT(v != sat::null_bool_var);
            SASSERT(!m.is_bool(e));
            expr_ref eq_th(m.mk_eq(a, th), m);
            expr_ref eq_el(m.mk_eq(a, el), m);
            sat::literal lit_th = internalize(eq_th, false, false, m_is_redundant);
            sat::literal lit_el = internalize(eq_el, false, false, m_is_redundant);
            literal lits1[2] = { literal(v, true),  lit_th };
            literal lits2[2] = { literal(v, false), lit_el };
            s().add_clause(2, lits1, st);
            s().add_clause(2, lits2, st);
        }
        else if (m.is_distinct(e)) {
            expr_ref_vector eqs(m);
            unsigned sz = n->num_args();
            for (unsigned i = 0; i < sz; ++i) {
                for (unsigned j = i + 1; j < sz; ++j) {
                    expr_ref eq(m.mk_eq(n->get_arg(i)->get_owner(), n->get_arg(j)->get_owner()), m);
                    eqs.push_back(eq);
                }
            }
            expr_ref fml(m.mk_or(eqs), m);
            sat::literal dist(m_expr2var.to_bool_var(e), false);
            sat::literal some_eq = si.internalize(fml, m_is_redundant);
            sat::literal lits1[2] = { ~dist, ~some_eq };
            sat::literal lits2[2] = { dist, some_eq };
            s().add_clause(2, lits1, st);
            s().add_clause(2, lits2, st);            
        }
    }

}
