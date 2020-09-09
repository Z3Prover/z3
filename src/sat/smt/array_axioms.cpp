/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    array_axioms.cpp

Abstract:

    Routines for instantiating array axioms

Author:

    Nikolaj Bjorner (nbjorner) 2020-09-08

--*/

#include "ast/ast_trail.h"
#include "ast/ast_ll_pp.h"
#include "sat/smt/array_solver.h"
#include "sat/smt/euf_solver.h"

namespace array {

    void solver::assert_axiom(axiom_record const& r) {
        app* child = r.n->get_app();
        app* select;
        switch (r.m_kind) {
        case axiom_record::kind_t::is_store:
            assert_store_axiom(child);
            break;
        case axiom_record::kind_t::is_select:
            select = r.select->get_app();
            SASSERT(a.is_select());
            if (a.is_const(child))
                assert_select_const_axiom(select, child);
            else if (a.is_as_array(child))
                assert_select_as_array_axiom(select, child);
            else if (a.is_store(child))
                assert_select_store_axiom(select, child);
            else if (a.is_map(child))
                assert_select_map_axiom(select, child);
            break;
        case axiom_record::kind_t::is_default:
            if (a.is_const(child))
                assert_default_const_axiom(child);
            else if (a.is_store(child))
                assert_default_store_axiom(child);
            else if (a.is_map(child))
                assert_default_map_axiom(child);
            else if (a.is_as_array(child))
                assert_default_as_array_axiom(child);
            break;
        case axiom_record::kind_t::is_extensionality:
            assert_extensionality(r.n->get_arg(0)->get_owner(), r.n->get_arg(1)->get_owner());
            break;
        default:
            UNREACHABLE();
            break;
        }
    }

    /**
     * Assert
     *    select(n, i) = v
     * Where
     *    n := store(a, i, v)
     */
    void solver::assert_store_axiom(app* e) {
        m_stats.m_num_store_axiom1++;
        SASSERT(a.is_store(e));
        unsigned num_args = e->get_num_args();
        ptr_vector<expr> sel_args(num_args - 1, e->get_args());
        sel_args[0] = e;
        expr_ref sel(a.mk_select(sel_args), m);
        euf::enode* n1 = e_internalize(sel);
        euf::enode* n2 = expr2enode(e->get_arg(num_args - 1));
        ctx.propagate(n1, n2, store_axiom());
    }


    /**
     * Assert
     *   i_k = j_k or select(store(a, i, v), j) = select(a, j)
     * where i = (i_1, ..., i_n), j = (j_1, .., j_n), k in 1..n
     */
    void solver::assert_select_store_axiom(app* select, app* store) {
        m_stats.m_num_store_axiom2a++;
        SASSERT(a.is_store(store));
        SASSERT(a.is_select(select));
        SASSERT(store->get_num_args() == 1 + select->get_num_args());
        ptr_buffer<expr> sel1_args, sel2_args;
        unsigned num_args = select->get_num_args();
        sel1_args.push_back(store);
        sel2_args.push_back(store->get_arg(0));

        for (unsigned i = 1; i < num_args; i++) {
            sel1_args.push_back(select->get_arg(i));
            sel2_args.push_back(select->get_arg(i));
        }

        expr_ref sel1(a.mk_select(sel1_args), m);
        expr_ref sel2(a.mk_select(sel2_args), m);
        expr_ref sel_eq_e(m.mk_eq(sel1, sel2), m);
        sat::literal sel_eq = b_internalize(sel_eq_e);

        for (unsigned i = 1; i < num_args; i++) {
            expr* idx1 = store->get_arg(i);
            expr* idx2 = select->get_arg(i);
            euf::enode* r1 = expr2enode(idx1)->get_root();
            euf::enode* r2 = expr2enode(idx2)->get_root();
            if (r1 == r2)
                continue;
            if (m.are_distinct(r1->get_owner(), r2->get_owner())) {
                add_clause(sel_eq);
                break;
            }
            sat::literal idx_eq = b_internalize(m.mk_eq(idx1, idx2));
            add_clause(idx_eq, sel_eq);
        }
    }

    /**
     * Assert
     *    select(const(v), i) = v
     */
    void solver::assert_select_const_axiom(app* select, app* cnst) {
        m_stats.m_num_select_const_axiom++;
        expr* val = nullptr;
        VERIFY(a.is_const(cnst, val));
        SASSERT(a.is_select(select));
        unsigned num_args = select->get_num_args();
        ptr_vector<expr> sel_args(num_args, select->get_args());
        sel_args[0] = cnst;
        expr_ref sel(a.mk_select(sel_args), m);
        euf::enode* n1 = e_internalize(sel);
        euf::enode* n2 = expr2enode(val);
        ctx.propagate(n1, n2, select_const_axiom());
    }


    /**
     * e1 = e2 or select(e1, diff(e1,e2)) != select(e2, diff(e1, e2))
     */
    void solver::assert_extensionality(expr* e1, expr* e2) {
        m_stats.m_num_extensionality_axiom++;
        func_decl_ref_vector* funcs = nullptr;
        VERIFY(m_sort2diff.find(m.get_sort(e1), funcs));
        expr_ref_vector args1(m), args2(m);
        args1.push_back(e1);
        args2.push_back(e2);
        for (func_decl* f : *funcs) {
            expr* k = m.mk_app(f, e1, e2);
            args1.push_back(k);
            args2.push_back(k);
        }
        expr_ref sel1(a.mk_select(args1), m);
        expr_ref sel2(a.mk_select(args2), m);
        expr_ref n1_eq_n2(m.mk_eq(e1, e2), m);
        expr_ref sel1_eq_sel2(m.mk_eq(sel1, sel2), m);
        literal lit1 = b_internalize(n1_eq_n2);
        literal lit2 = b_internalize(sel1_eq_sel2);
        add_clause(lit1, ~lit2);
    }

    /**
    * Assert axiom:
    * select(map[f](a, ... d), i) = f(select(a,i),...,select(d,i))
    */
    void solver::assert_select_map_axiom(app* select, app* map) {
        m_stats.m_num_map_axiom++;
        SASSERT(a.is_map(map));
        SASSERT(a.is_select(select));
        SASSERT(map->get_num_args() > 0);
        func_decl* f = a.get_map_func_decl(map);

        TRACE("array",
            tout << mk_bounded_pp(map, m) << "\n";
        tout << mk_bounded_pp(select, m) << "\n";);
        unsigned num_args = select->get_num_args();
        unsigned num_arrays = map->get_num_args();
        ptr_buffer<expr> args1, args2;
        vector<ptr_vector<expr> > args2l;
        args1.push_back(map);
        for (expr* ar : *map) {
            ptr_vector<expr> arg;
            arg.push_back(ar);
            args2l.push_back(arg);
        }
        for (unsigned i = 1; i < num_args; ++i) {
            expr* arg = select->get_arg(i);
            for (auto& args : args2l)
                args.push_back(arg);
            args1.push_back(arg);
        }
        for (auto const& args : args2l)
            args2.push_back(a.mk_select(args));

        expr_ref sel1(m), sel2(m);
        sel1 = a.mk_select(args1);
        sel2 = m.mk_app(f, args2);
        rewrite(sel2);
        ctx.propagate(e_internalize(sel1), e_internalize(sel2), map_axiom());
    }


    /**
     * Assert axiom:
     * select(as-array f, i_1, ..., i_n) = (f i_1 ... i_n)
     */
    void solver::assert_select_as_array_axiom(app* select, app* arr) {
        m_stats.m_num_select_as_array_axiom++;
        SASSERT(a.is_as_array(arr));
        SASSERT(a.is_select(select));
        unsigned num_args = select->get_num_args();
        func_decl* f = a.get_as_array_func_decl(arr);
        ptr_vector<expr> sel_args(num_args, select->get_args());
        sel_args[0] = arr;
        expr_ref sel(a.mk_select(sel_args), m);
        expr_ref val(m.mk_app(f, sel_args.size() - 1, sel_args.c_ptr() + 1), m);
        ctx.propagate(e_internalize(val), e_internalize(sel), select_as_array_axiom());
    }

    /**
     * Assert:
     *    default(map[f](a,..,d)) = f(default(a),..,default(d))
     */
    void solver::assert_default_map_axiom(app* map) {
        m_stats.m_num_default_map_axiom++;
        SASSERT(a.is_map(map));
        func_decl* f = a.get_map_func_decl(map);
        SASSERT(map->get_num_args() == f->get_arity());
        ptr_buffer<expr> args2;
        for (expr* arg : *map)
            args2.push_back(a.mk_default(arg));

        expr_ref def1(a.mk_default(map), m);
        expr_ref def2(m.mk_app(f, args2), m);
        rewrite(def2);
        ctx.propagate(e_internalize(def1), e_internalize(def2), default_map_axiom());
    }


    /**
     * Assert:
     *    default(const(e)) = e
     */
    void solver::assert_default_const_axiom(app* cnst) {
        m_stats.m_num_default_const_axiom++;
        expr* val = nullptr;
        VERIFY(a.is_const(cnst, val));
        TRACE("array", tout << mk_bounded_pp(cnst, m) << "\n";);
        expr_ref def(a.mk_default(cnst), m);
        ctx.propagate(expr2enode(val), e_internalize(def), default_const_axiom());
    }

    void solver::assert_default_as_array_axiom(app* as_array) {
        // no-op
    }


    /**
     * let n := store(a, i, v)
     * Assert:
     * - when sort(n) has exactly one element:
     *      default(n) = v
     * - for small domains:
     *     default(n) = ite(epsilon1 = i, v, default(a))
           n[diag(i)] = a[diag(i)]
     * - for large domains:
     *     default(n) = default(a)
     */
    void solver::assert_default_store_axiom(app* store) {
        m_stats.m_num_default_store_axiom++;
        SASSERT(a.is_store(store));
        SASSERT(store->get_num_args() >= 3);
        expr_ref def1(m), def2(m);

        unsigned num_args = store->get_num_args();

        def1 = a.mk_default(store);
        def2 = a.mk_default(store->get_arg(0));

        bool is_new = false;

        if (has_unitary_domain(store)) {
            def2 = store->get_arg(num_args - 1);
        }
        else if (!has_large_domain(store)) {
            //
            // let A = store(B, i, v)
            // 
            // Add:
            //   default(A) = ite(epsilon1 = i, v, default(B))
            //   A[diag(i)] = B[diag(i)]
            // 
            expr_ref_vector eqs(m);
            expr_ref_vector args1(m), args2(m);
            args1.push_back(store->get_arg(0));
            args2.push_back(store);

            for (unsigned i = 1; i + 1 < num_args; ++i) {
                expr* arg = store->get_arg(i);
                sort* srt = m.get_sort(arg);
                auto ep = mk_epsilon(srt);
                eqs.push_back(m.mk_eq(ep.first, arg));
                args1.push_back(m.mk_app(ep.second, arg));
                args2.push_back(m.mk_app(ep.second, arg));
            }
            expr_ref eq(m.mk_and(eqs), m);
            def2 = m.mk_ite(eq, store->get_arg(num_args - 1), def2);
            app_ref sel1(m), sel2(m);
            sel1 = a.mk_select(args1);
            sel2 = a.mk_select(args2);
            ctx.propagate(e_internalize(sel1), e_internalize(sel2), default_store_axiom());
        }
        ctx.propagate(e_internalize(def1), e_internalize(def2), default_store_axiom());
    }


    bool solver::has_unitary_domain(app* array_term) {
        SASSERT(a.is_array(array_term));
        sort* s = m.get_sort(array_term);
        unsigned dim = get_array_arity(s);
        for (unsigned i = 0; i < dim; ++i) {
            sort* d = get_array_domain(s, i);
            if (d->is_infinite() || d->is_very_big() || 1 != d->get_num_elements().size())
                return false;
        }
        return true;
    }

    bool solver::has_large_domain(app* array_term) {
        SASSERT(a.is_array(array_term));
        sort* s = m.get_sort(array_term);
        unsigned dim = get_array_arity(s);
        rational sz(1);
        for (unsigned i = 0; i < dim; ++i) {
            sort* d = get_array_domain(s, i);
            if (d->is_infinite() || d->is_very_big()) {
                return true;
            }
            sz *= rational(d->get_num_elements().size(), rational::ui64());
            if (sz >= rational(1 << 14)) {
                return true;
            }
        }
        return false;
    }


    std::pair<app*, func_decl*> solver::mk_epsilon(sort* s) {
        app* eps = nullptr;
        func_decl* diag = nullptr;
        if (!m_sort2epsilon.find(s, eps)) {
            eps = m.mk_fresh_const("epsilon", s);
            ctx.push(ast2ast_trail<euf::solver, sort, app>(m_sort2epsilon, s, eps));
        }
        if (!m_sort2diag.find(s, diag)) {
            diag = m.mk_fresh_func_decl("diag", 1, &s, s);
            ctx.push(ast2ast_trail<euf::solver, sort, func_decl>(m_sort2diag, s, diag));
        }
        return std::make_pair(eps, diag);
    }



}

