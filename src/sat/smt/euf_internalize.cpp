/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    euf_internalize.cpp

Abstract:

    Internalize utilities for EUF solver plugin.

Author:

    Nikolaj Bjorner (nbjorner) 2020-08-25

Notes:

(*) From smt_internalizer.cpp
    This code is necessary because some theories may decide
    not to create theory variables for a nested application.
    Example:
      Suppose (+ (* 2 x) y) is internalized by arithmetic
      and an enode is created for the + and * applications,
      but a theory variable is only created for the + application.
      The (* 2 x) is internal to the arithmetic module.
      Later, the core tries to internalize (f (* 2 x)).
      Now, (* 2 x) is not internal to arithmetic anymore,
     and a theory variable must be created for it.

--*/

#include "ast/pb_decl_plugin.h"
#include "sat/smt/euf_solver.h"

namespace euf {

    void solver::internalize(expr* e, bool redundant) {
        if (get_enode(e))
            return;
        if (si.is_bool_op(e))
            attach_lit(si.internalize(e, redundant), e);
        else if (auto* ext = expr2solver(e))
            ext->internalize(e, redundant);
        else
            visit_rec(m, e, false, false, redundant);
        SASSERT(m_egraph.find(e));
    }

    sat::literal solver::mk_literal(expr* e) {
        expr_ref _e(e, m);
        bool is_not = m.is_not(e, e);
        sat::literal lit = internalize(e, false, false, m_is_redundant);
        if (is_not)
            lit.neg();
        return lit;
    }

    sat::literal solver::internalize(expr* e, bool sign, bool root, bool redundant) {
        euf::enode* n = get_enode(e);
        if (n) {
            if (m.is_bool(e)) {
                SASSERT(!s().was_eliminated(n->bool_var()));
                SASSERT(n->bool_var() != sat::null_bool_var);
                return literal(n->bool_var(), sign);
            }
            TRACE("euf", tout << "non-bool\n";);
            return sat::null_literal;
        }
        if (si.is_bool_op(e)) {
            sat::literal lit = attach_lit(si.internalize(e, redundant), e);
            if (sign) 
                lit.neg();
            return lit;
        }
        if (auto* ext = expr2solver(e))
            return ext->internalize(e, sign, root, redundant);
        if (!visit_rec(m, e, sign, root, redundant)) {
            TRACE("euf", tout << "visit-rec\n";);          
            return sat::null_literal;
        }
        SASSERT(get_enode(e));
        if (m.is_bool(e))
            return literal(si.to_bool_var(e), sign);
        return sat::null_literal;
    }

    bool solver::visit(expr* e) {
        euf::enode* n = m_egraph.find(e);
        th_solver* s = nullptr;        
        if (n && !si.is_bool_op(e) && (s = expr2solver(e), s && euf::null_theory_var == n->get_th_var(s->get_id()))) {
            // ensure that theory variables are attached in shared contexts. See notes (*)
            s->internalize(e, false);
            return true;
        }
        if (n)
            return true;
        if (si.is_bool_op(e)) {
            attach_lit(si.internalize(e, m_is_redundant), e);
            return true;
        }
        if (is_app(e) && to_app(e)->get_num_args() > 0) {
            m_stack.push_back(sat::eframe(e));
            return false;
        }        
        if (auto* s = expr2solver(e))
            s->internalize(e, m_is_redundant);            
        else 
            attach_node(mk_enode(e, 0, nullptr));        
        return true;
    }

    bool solver::post_visit(expr* e, bool sign, bool root) {
        unsigned num = is_app(e) ? to_app(e)->get_num_args() : 0;
        m_args.reset();
        for (unsigned i = 0; i < num; ++i)
            m_args.push_back(m_egraph.find(to_app(e)->get_arg(i)));
        if (root && internalize_root(to_app(e), sign, m_args))
            return false;
        SASSERT(!get_enode(e));
        if (auto* s = expr2solver(e)) 
            s->internalize(e, m_is_redundant);        
        else 
            attach_node(mk_enode(e, num, m_args.data()));        
        return true;
    }

    bool solver::visited(expr* e) {
        return m_egraph.find(e) != nullptr;
    }

    void solver::attach_node(euf::enode* n) {
        expr* e = n->get_expr();
        if (m.is_bool(e))
            attach_lit(literal(si.add_bool_var(e), false), e);

        if (!m.is_bool(e) && !m.is_uninterp(e->get_sort())) {
            auto* e_ext = expr2solver(e);
            auto* s_ext = sort2solver(e->get_sort());
            if (s_ext && s_ext != e_ext)
                s_ext->apply_sort_cnstr(n, e->get_sort());
            else if (!s_ext && !e_ext && is_app(e)) 
                unhandled_function(to_app(e)->get_decl());
        }
        expr* a = nullptr, * b = nullptr;                   
        if (m.is_eq(e, a, b) && a->get_sort()->get_family_id() != null_family_id) {
            auto* s_ext = sort2solver(a->get_sort());
            if (s_ext)
                s_ext->eq_internalized(n);
        }
        axiomatize_basic(n);
    }

    sat::literal solver::attach_lit(literal lit, expr* e) {
        sat::bool_var v = lit.var();       
        s().set_external(v);
        s().set_eliminated(v, false);           

        if (lit.sign()) {
            v = si.add_bool_var(e);
            s().set_external(v);
            s().set_eliminated(v, false);
            sat::literal lit2 = literal(v, false);
            s().mk_clause(~lit, lit2, sat::status::th(m_is_redundant, m.get_basic_family_id()));
            s().mk_clause(lit, ~lit2, sat::status::th(m_is_redundant, m.get_basic_family_id()));
            add_aux(~lit, lit2);
            add_aux(lit, ~lit2);
            lit = lit2;
        }

        TRACE("euf", tout << "attach " << v << " " << mk_bounded_pp(e, m) << "\n";);
        m_bool_var2expr.reserve(v + 1, nullptr);
        if (m_bool_var2expr[v] && m_egraph.find(e)) {
            if (m_egraph.find(e)->bool_var() != v) {
                IF_VERBOSE(0, verbose_stream()
                 << "var " << v << "\n"
                 << "found var " << m_egraph.find(e)->bool_var() << "\n"
                 << mk_pp(m_bool_var2expr[v], m) << "\n"
                 << mk_pp(e, m) << "\n");
            }
            SASSERT(m_egraph.find(e)->bool_var() == v);
            return lit;
        }

        m_bool_var2expr[v] = e;
        m_var_trail.push_back(v);        
        enode* n = m_egraph.find(e);
        if (!n) 
            n = mk_enode(e, 0, nullptr);
        SASSERT(n->bool_var() == sat::null_bool_var || n->bool_var() == v);
        m_egraph.set_bool_var(n, v);
        if (m.is_eq(e) || m.is_or(e) || m.is_and(e) || m.is_not(e))
            m_egraph.set_merge_enabled(n, false);
        lbool val = s().value(lit);
        if (val != l_undef) 
            m_egraph.set_value(n, val, justification::external(to_ptr(val == l_true ? lit : ~lit)));
        return lit;
    }

    bool solver::internalize_root(app* e, bool sign, enode_vector const& args) {
        if (m.is_distinct(e)) {
            enode_vector _args(args);
            if (sign)
                add_not_distinct_axiom(e, _args.data());
            else
                add_distinct_axiom(e, _args.data());
            return true;
        }
        return false;
    }

    void solver::add_not_distinct_axiom(app* e, enode* const* args) {
        SASSERT(m.is_distinct(e));
        unsigned sz = e->get_num_args();
        sat::status st = sat::status::th(m_is_redundant, m.get_basic_family_id());

        if (sz <= 1) {
            s().mk_clause(0, nullptr, st);
            return;
        }

        static const unsigned distinct_max_args = 32;
        if (sz <= distinct_max_args) {
            sat::literal_vector lits;
            for (unsigned i = 0; i < sz; ++i) {
                for (unsigned j = i + 1; j < sz; ++j) {
                    expr_ref eq = mk_eq(args[i]->get_expr(), args[j]->get_expr());
                    sat::literal lit = mk_literal(eq);
                    lits.push_back(lit);
                }
            }
            add_root(lits);
            s().mk_clause(lits, st);
        }
        else {
            // g(f(x_i)) = x_i
            // f(x_1) = a + .... + f(x_n) = a >= 2
            sort* srt = e->get_arg(0)->get_sort();
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
                expr_ref eq = mk_eq(gapp, arg);
                sat::literal lit = mk_literal(eq);
                s().add_clause(lit, st);
                eqs.push_back(mk_eq(fapp, a));
            }
            pb_util pb(m);
            expr_ref at_least2(pb.mk_at_least_k(eqs.size(), eqs.data(), 2), m);
            sat::literal lit = si.internalize(at_least2, m_is_redundant);
            s().add_clause(lit, st);
        }
    }

    void solver::add_distinct_axiom(app* e, enode* const* args) {
        SASSERT(m.is_distinct(e));
        static const unsigned distinct_max_args = 32;
        unsigned sz = e->get_num_args();
        sat::status st = sat::status::th(m_is_redundant, m.get_basic_family_id());
        if (sz <= 1) 
            return;
        if (sz <= distinct_max_args) {
            for (unsigned i = 0; i < sz; ++i) {
                for (unsigned j = i + 1; j < sz; ++j) {
                    expr_ref eq = mk_eq(args[i]->get_expr(), args[j]->get_expr());
                    sat::literal lit = ~mk_literal(eq);
                    s().add_clause(lit, st);
                }
            }
        }
        else {
            // dist-f(x_1) = v_1 & ... & dist-f(x_n) = v_n
            sort* srt = e->get_arg(0)->get_sort();
            SASSERT(!m.is_bool(srt));
            sort_ref u(m.mk_fresh_sort("distinct-elems"), m);
            func_decl_ref f(m.mk_fresh_func_decl("dist-f", "", 1, &srt, u), m);
            for (unsigned i = 0; i < sz; ++i) {
                expr_ref fapp(m.mk_app(f, e->get_arg(i)), m);
                expr_ref fresh(m.mk_fresh_const("dist-value", u), m);
                enode* n = mk_enode(fresh, 0, nullptr);
                n->mark_interpreted();
                expr_ref eq = mk_eq(fapp, fresh);
                sat::literal lit = mk_literal(eq);
                s().add_clause(lit, st);
            }
        }
    }

    void solver::axiomatize_basic(enode* n) {
        expr* e = n->get_expr();
        sat::status st = sat::status::th(m_is_redundant, m.get_basic_family_id());
        expr* c = nullptr, * th = nullptr, * el = nullptr;
        if (!m.is_bool(e) && m.is_ite(e, c, th, el)) {
            expr_ref eq_th = mk_eq(e, th);
            sat::literal lit_th = mk_literal(eq_th);
            if (th == el) {
                s().add_clause(lit_th, st);
            }
            else {
                sat::literal lit_c = mk_literal(c);
                expr_ref eq_el = mk_eq(e, el);
                sat::literal lit_el = mk_literal(eq_el);
                add_root(~lit_c, lit_th);
                add_root(lit_c, lit_el);
                s().add_clause(~lit_c, lit_th, st);
                s().add_clause(lit_c, lit_el, st);
            }
        }
        else if (m.is_distinct(e)) {
            // TODO - add lazy case for large values of sz.
            expr_ref_vector eqs(m);
            unsigned sz = n->num_args();
            for (unsigned i = 0; i < sz; ++i) {
                for (unsigned j = i + 1; j < sz; ++j) {
                    expr_ref eq = mk_eq(n->get_arg(i)->get_expr(), n->get_arg(j)->get_expr());
                    eqs.push_back(eq);
                }
            }
            expr_ref fml(m.mk_or(eqs), m);
            sat::literal dist(si.to_bool_var(e), false);
            sat::literal some_eq = si.internalize(fml, m_is_redundant);
            add_root(~dist, ~some_eq);
            add_root(dist, some_eq);
            s().add_clause(~dist, ~some_eq, st);
            s().add_clause(dist, some_eq, st);
        }
        else if (m.is_eq(e, th, el) && !m.is_iff(e)) {
            sat::literal lit1 = expr2literal(e);
            s().set_phase(lit1);
            expr_ref e2(m.mk_eq(el, th), m);
            enode* n2 = m_egraph.find(e2);
            if (n2) {
                sat::literal lit2 = expr2literal(e2);
                add_root(~lit1, lit2);
                add_root(lit1, ~lit2);
                s().add_clause(~lit1, lit2, st);
                s().add_clause(lit1, ~lit2, st);
            }
        }
    }


    bool solver::is_shared(enode* n) const {
        n = n->get_root();

        if (m.is_ite(n->get_expr()))
            return true;

        // the variable is shared if the equivalence class of n
        // contains a parent application.
        
        family_id th_id = m.get_basic_family_id();
        for (auto const& p : euf::enode_th_vars(n)) {
            family_id id = p.get_id();
            if (m.get_basic_family_id() != id) {
                if (th_id != m.get_basic_family_id())
                    return true;
                th_id = id;               
            }
        }
        if (m.is_bool(n->get_expr()) && th_id != m.get_basic_family_id())
            return true;
        
        for (enode* parent : euf::enode_parents(n)) {
            app* p = to_app(parent->get_expr());
            family_id fid = p->get_family_id();
            if (fid != th_id && fid != m.get_basic_family_id())
                return true;
        }

        // Some theories implement families of theories. Examples:
        // Arrays and Tuples.  For example, array theory is a
        // parametric theory, that is, it implements several theories:
        // (array int int), (array int (array int int)), ...
        //
        // Example:
        //
        // a : (array int int)
        // b : (array int int)
        // x : int
        // y : int
        // v : int
        // w : int
        // A : (array (array int int) int)
        //
        // assert (= b (store a x v))
        // assert (= b (store a y w))
        // assert (not (= x y))
        // assert (not (select A a))
        // assert (not (select A b))
        // check
        //
        // In the example above, 'a' and 'b' are shared variables between
        // the theories of (array int int) and (array (array int int) int).
        // Remark: The inconsistency is not going to be detected if they are
        // not marked as shared.

        for (auto const& p : euf::enode_th_vars(n)) 
            if (fid2solver(p.get_id())->is_shared(p.get_var()))
                return true;

        return false;
    }

    expr_ref solver::mk_eq(expr* e1, expr* e2) {
        expr_ref _e1(e1, m);
        expr_ref _e2(e2, m);
        if (m.are_equal(e1, e2))
            return expr_ref(m.mk_true(), m);
        if (m.are_distinct(e1, e2))
            return expr_ref(m.mk_false(), m);
        expr_ref r(m.mk_eq(e2, e1), m);
        if (!m_egraph.find(r))
            r = m.mk_eq(e1, e2);
        return r;
    }

    unsigned solver::get_max_generation(expr* e) const {
        unsigned g = 0;
        expr_fast_mark1 mark;
        m_todo.push_back(e);
        while (!m_todo.empty()) {
            e = m_todo.back();
            m_todo.pop_back();
            if (mark.is_marked(e))
                continue;
            mark.mark(e);
            euf::enode* n = m_egraph.find(e);
            if (n) 
                g = std::max(g, n->generation());
            else if (is_app(e)) 
                for (expr* arg : *to_app(e))
                    m_todo.push_back(arg);
        }
        return g;
    }

    euf::enode* solver::e_internalize(expr* e) {
        euf::enode* n = m_egraph.find(e);
        if (!n) {
            internalize(e, m_is_redundant);
            n = m_egraph.find(e);
        }
        return n;
    }

    euf::enode* solver::mk_enode(expr* e, unsigned n, enode* const* args) { 
        euf::enode* r = m_egraph.mk(e, m_generation, n, args); 
        for (unsigned i = 0; i < n; ++i)
            ensure_merged_tf(args[i]);
        return r;
    }

    void solver::ensure_merged_tf(euf::enode* n) {
        switch (n->value()) {
        case l_undef:
            break;
        case l_true:
            if (n->get_root() != mk_true())
                m_egraph.merge(n, mk_true(), to_ptr(sat::literal(n->bool_var())));
            break;
        case l_false:
            if (n->get_root() != mk_false())
                m_egraph.merge(n, mk_false(), to_ptr(~sat::literal(n->bool_var())));
            break;
        }
    }

}
