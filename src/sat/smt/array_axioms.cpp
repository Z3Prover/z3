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

    struct solver::reset_new : trail {
        solver& s;
        unsigned m_idx;
        reset_new(solver& s, unsigned idx) : s(s), m_idx(idx) {}
        void undo() override {
            s.m_axiom_trail[m_idx].set_new();
        }
    };

    void solver::push_axiom(axiom_record const& r) { 
        unsigned idx = m_axiom_trail.size();
        m_axiom_trail.push_back(r); 
        TRACE("array", display(tout, r) << " " << m_axioms.contains(idx) << "\n";);
        if (m_axioms.contains(idx))
            m_axiom_trail.pop_back();
        else {
            m_axioms.insert(idx);
            ctx.push(push_back_vector<svector<axiom_record>>(m_axiom_trail));
            ctx.push(insert_map<axiom_table_t, unsigned>(m_axioms, idx));
        }
    }

    bool solver::propagate_axiom(unsigned idx) {        
        if (is_applied(idx))
            return false;
        bool st = assert_axiom(idx);
        if (!is_delayed(idx)) {
            ctx.push(reset_new(*this, idx));
            set_applied(idx);
        }
        return st;
    }

    bool solver::assert_axiom(unsigned idx) {
        axiom_record& r = m_axiom_trail[idx];
        switch (r.m_kind) {
        case axiom_record::kind_t::is_store:
            return assert_store_axiom(r.n->get_app());
        case axiom_record::kind_t::is_select:
            return assert_select(idx, r);
        case axiom_record::kind_t::is_default:
            return assert_default(r);
        case axiom_record::kind_t::is_extensionality:
            return assert_extensionality(r.n->get_expr(), r.select->get_expr());
        case axiom_record::kind_t::is_congruence:
            return assert_congruent_axiom(r.n->get_expr(), r.select->get_expr());
        default:
            UNREACHABLE();
            break;
        }
        return false;
    }

    bool solver::assert_default(axiom_record& r) {
        expr* child = r.n->get_expr();
        SASSERT(can_beta_reduce(r.n));
            
        TRACE("array", tout << "default-axiom: " << mk_bounded_pp(child, m, 2) << "\n";);
        if (a.is_const(child))
            return assert_default_const_axiom(to_app(child));
        else if (a.is_store(child))
            return assert_default_store_axiom(to_app(child));
        else if (is_map_combinator(child))
            return assert_default_map_axiom(to_app(child));
        else
            return false;                
    }

    bool solver::assert_select(unsigned idx, axiom_record& r) {
        expr* child = r.n->get_expr();
        app* select = r.select->get_app();
        SASSERT(a.is_select(select));
        SASSERT(can_beta_reduce(r.n));

        bool should_delay = 
            get_config().m_array_delay_exp_axiom && 
            r.select->get_arg(0)->get_root() != r.n->get_root() && 
            !r.is_delayed() && m_enable_delay;

        TRACE("array", display(tout << "select-axiom: " << (should_delay ? "delay " : ""), r) << "\n";);

        if (should_delay) {
            IF_VERBOSE(11, verbose_stream() << "delay: " << mk_bounded_pp(child, m) << " " << mk_bounded_pp(select, m) << "\n");
            ctx.push(reset_new(*this, idx));
            r.set_delayed();
            return false;
        }
        if (a.is_const(child))
            return assert_select_const_axiom(select, to_app(child));
        else if (a.is_as_array(child))
            return assert_select_as_array_axiom(select, to_app(child));
        else if (a.is_store(child))
            return assert_select_store_axiom(select, to_app(child));
        else if (is_map_combinator(child))
            return assert_select_map_axiom(select, to_app(child));
        else if (is_lambda(child))
            return assert_select_lambda_axiom(select, child);
        else
            UNREACHABLE();
        return false;
    }

    /**
     * Assert
     *    select(n, i) = v
     * Where
     *    n := store(a, i, v)
     */
    bool solver::assert_store_axiom(app* e) {
        TRACE("array", tout << "store-axiom: " << mk_bounded_pp(e, m) << "\n";);
        ++m_stats.m_num_store_axiom;
        SASSERT(a.is_store(e));
        unsigned num_args = e->get_num_args();
        ptr_vector<expr> sel_args(num_args - 1, e->get_args());
        sel_args[0] = e;
        expr_ref sel(a.mk_select(sel_args), m);
        euf::enode* n1 = e_internalize(sel);
        euf::enode* n2 = expr2enode(e->get_arg(num_args - 1));
        return ctx.propagate(n1, n2, array_axiom());
    }


    /**
     * Assert
     *   i_k = j_k or select(store(a, i, v), j) = select(a, j)
     * where i = (i_1, ..., i_n), j = (j_1, .., j_n), k in 1..n
     */
    bool solver::assert_select_store_axiom(app* select, app* store) {
        SASSERT(a.is_store(store));
        SASSERT(a.is_select(select));
        SASSERT(store->get_num_args() == 1 + select->get_num_args());
        ptr_buffer<expr> sel1_args, sel2_args;
        unsigned num_args = select->get_num_args();

        bool has_diff = false;
        for (unsigned i = 1; i < num_args; i++) 
            has_diff |= expr2enode(select->get_arg(i))->get_root() != expr2enode(store->get_arg(i))->get_root();
        if (!has_diff)
            return false;

        sel1_args.push_back(store);
        sel2_args.push_back(store->get_arg(0));       
        
        for (unsigned i = 1; i < num_args; i++) {
            sel1_args.push_back(select->get_arg(i));
            sel2_args.push_back(select->get_arg(i));
        }
   
        expr_ref sel1(a.mk_select(sel1_args), m);
        expr_ref sel2(a.mk_select(sel2_args), m);
        expr_ref sel_eq_e(m.mk_eq(sel1, sel2), m);

        bool new_prop = false;
        if (!ctx.get_egraph().find(sel1))
            new_prop = true;
        if (!ctx.get_egraph().find(sel2))
            new_prop = true;

        euf::enode* s1 = e_internalize(sel1);
        euf::enode* s2 = e_internalize(sel2);
        TRACE("array", 
              tout << "select-store " << ctx.bpp(s1) << " " << ctx.bpp(s1->get_root()) << "\n";
              tout << "select-store " << ctx.bpp(s2) << " " << ctx.bpp(s2->get_root()) << "\n";);

        if (s1->get_root() == s2->get_root())
            return new_prop;
        
        sat::literal sel_eq = sat::null_literal;
        auto ensure_relevant = [&](sat::literal lit) {
            if (ctx.is_relevant(lit))
                return;
            new_prop = true;
            ctx.mark_relevant(lit);            
        };
        auto init_sel_eq = [&]() {
            if (sel_eq != sat::null_literal) 
                return true;
            sel_eq = mk_literal(sel_eq_e);
            ensure_relevant(sel_eq);
            return s().value(sel_eq) != l_true;
        };

        for (unsigned i = 1; i < num_args; i++) {
            expr* idx1 = store->get_arg(i);
            expr* idx2 = select->get_arg(i);
            euf::enode* r1 = expr2enode(idx1);
            euf::enode* r2 = expr2enode(idx2);
            if (r1 == r2)
                continue;
            if (m.are_distinct(r1->get_expr(), r2->get_expr())) {
                if (init_sel_eq() && add_clause(sel_eq))
                    new_prop = true;
                break;
            }
            sat::literal idx_eq = eq_internalize(idx1, idx2);
            ensure_relevant(idx_eq);
            if (s().value(idx_eq) == l_true)
                continue;
            if (s().value(idx_eq) == l_undef)
                new_prop = true;
            if (!init_sel_eq())
                break;
            if (add_clause(idx_eq, sel_eq))
                new_prop = true;
        }
        ++m_stats.m_num_select_store_axiom;
        TRACE("array", tout << "select-stored " << new_prop << "\n";);
        return new_prop;
    }

    /**
     * Assert
     *    select(const(v), i) = v
     */
    bool solver::assert_select_const_axiom(app* select, app* cnst) {        
        ++m_stats.m_num_select_const_axiom;
        expr* val = nullptr;
        VERIFY(a.is_const(cnst, val));
        SASSERT(a.is_select(select));
        unsigned num_args = select->get_num_args();
        ptr_vector<expr> sel_args(num_args, select->get_args());
        sel_args[0] = cnst;
        expr_ref sel(a.mk_select(sel_args), m);
        euf::enode* n1 = e_internalize(sel);
        euf::enode* n2 = expr2enode(val);
        return ctx.propagate(n1, n2, array_axiom());
    }


    /**
     * e1 = e2 or select(e1, diff(e1,e2)) != select(e2, diff(e1, e2))
     */
    bool solver::assert_extensionality(expr* e1, expr* e2) {
        ++m_stats.m_num_extensionality_axiom;
        func_decl_ref_vector const& funcs = sort2diff(e1->get_sort());
        expr_ref_vector args1(m), args2(m);
        args1.push_back(e1);
        args2.push_back(e2);
        for (func_decl* f : funcs) {
            expr_ref k(m.mk_app(f, e1, e2), m);
            rewrite(k);
            args1.push_back(k);
            args2.push_back(k);
        }
        expr_ref sel1(a.mk_select(args1), m);
        expr_ref sel2(a.mk_select(args2), m);
        literal lit1 = eq_internalize(e1, e2);
        literal lit2 = eq_internalize(sel1, sel2);
        TRACE("array", tout << "extensionality-axiom: " << mk_bounded_pp(e1, m) << " == " << mk_bounded_pp(e2, m) << "\n" << lit1 << " " << ~lit2 << "\n";);
        return add_clause(lit1, ~lit2);
    }

    bool solver::is_map_combinator(expr* map) const {
        return a.is_map(map) || a.is_union(map) || a.is_intersect(map) || a.is_difference(map) || a.is_complement(map);
    }

    /**
    * Assert axiom:
    * select(map[f](a, ... d), i) = f(select(a,i),...,select(d,i))
    */
    bool solver::assert_select_map_axiom(app* select, app* map) {
        ++m_stats.m_num_select_map_axiom;
        SASSERT(a.is_select(select));
        SASSERT(is_map_combinator(map));
        SASSERT(map->get_num_args() > 0);
        unsigned num_args = select->get_num_args();
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
        sel2 = apply_map(map, args2.size(), args2.data());

        rewrite(sel2); 
        euf::enode* n1 = e_internalize(sel1);
        euf::enode* n2 = e_internalize(sel2);
        return ctx.propagate(n1, n2, array_axiom());
   }


    /**
     * Assert axiom:
     * select(as-array f, i_1, ..., i_n) = (f i_1 ... i_n)
     */
    bool solver::assert_select_as_array_axiom(app* select, app* arr) {
        ++m_stats.m_num_select_as_array_axiom;
        SASSERT(a.is_as_array(arr));
        SASSERT(a.is_select(select));
        unsigned num_args = select->get_num_args();
        func_decl* f = a.get_as_array_func_decl(arr);
        ptr_vector<expr> sel_args(num_args, select->get_args());
        sel_args[0] = arr;
        expr_ref sel(a.mk_select(sel_args), m);
        expr_ref val(m.mk_app(f, sel_args.size() - 1, sel_args.data() + 1), m);
        euf::enode* n1 = e_internalize(sel);
        euf::enode* n2 = e_internalize(val);
        return ctx.propagate(n1, n2, array_axiom());
    }

    expr_ref solver::apply_map(app* map, unsigned n, expr* const* args) {
        expr_ref result(m);
        if (a.is_map(map)) 
            result = m.mk_app(a.get_map_func_decl(map), n, args);
        else if (a.is_union(map)) 
            result = m.mk_or(n, args);
        else if (a.is_intersect(map)) 
            result = m.mk_and(n, args);
        else if (a.is_difference(map)) {
            SASSERT(n > 0);
            result = args[0];
            for (unsigned i = 1; i < n; ++i)
                result = m.mk_and(result, m.mk_not(args[i]));
        }
        else if (a.is_complement(map)) {
            SASSERT(n == 1);
            result = m.mk_not(args[0]);
        }
        else {            
            UNREACHABLE();
        }
        rewrite(result);
        return result;
    }


    /**
     * Assert:
     *    default(map[f](a,..,d)) = f(default(a),..,default(d))
     */
    bool solver::assert_default_map_axiom(app* map) {
        ++m_stats.m_num_default_map_axiom;
        SASSERT(is_map_combinator(map));
        expr_ref_vector args2(m);
        for (expr* arg : *map)
            args2.push_back(a.mk_default(arg));
        expr_ref def1(a.mk_default(map), m);
        expr_ref def2 = apply_map(map, args2.size(), args2.data());
        return ctx.propagate(e_internalize(def1), e_internalize(def2), array_axiom());
    }

    /**
     * Assert:
     *    default(const(e)) = e
     */
    bool solver::assert_default_const_axiom(app* cnst) {
        ++m_stats.m_num_default_const_axiom;
        expr* val = nullptr;
        VERIFY(a.is_const(cnst, val));
        expr_ref def(a.mk_default(cnst), m);
        return ctx.propagate(expr2enode(val), e_internalize(def), array_axiom());
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
    bool solver::assert_default_store_axiom(app* store) {
        ++m_stats.m_num_default_store_axiom;
        SASSERT(a.is_store(store));
        SASSERT(store->get_num_args() >= 3);
        expr_ref def1(m), def2(m);
        bool prop = false;
        unsigned num_args = store->get_num_args();
        def1 = a.mk_default(store);
        def2 = a.mk_default(store->get_arg(0));

        prop |= !ctx.get_enode(def1) || !ctx.get_enode(def2);

        euf::enode* ndef1 = e_internalize(def1);
        euf::enode* ndef2 = e_internalize(def2);

        if (has_unitary_domain(store)) {
            def2 = store->get_arg(num_args - 1);
        }
        else if (!has_large_domain(store)) {
            //
            // let A = store(B, i, v)
            // 
            // Add:
            //   default(A) = A[epsilon]
            //   default(B) = B[epsilon]
            // 
            expr_ref_vector eqs(m);
            expr_ref_vector args1(m), args2(m);
            args1.push_back(store->get_arg(0));
            args2.push_back(store);

            for (unsigned i = 1; i + 1 < num_args; ++i) {
                expr* arg = store->get_arg(i);
                sort* srt = arg->get_sort();
                auto [ep, d] = mk_epsilon(srt);
                eqs.push_back(m.mk_eq(ep, arg));
                args1.push_back(ep);
                args2.push_back(ep);
            }
            app_ref sel1(m), sel2(m);
            sel1 = a.mk_select(args1);
            sel2 = a.mk_select(args2);
            return 
                ctx.propagate(e_internalize(sel1), ndef1, array_axiom()) ||
                ctx.propagate(e_internalize(sel2), ndef2, array_axiom()) ||
                prop;
        }
        // default(A) == default(B)
        if (ctx.propagate(ndef1, ndef2, array_axiom()))
            prop = true;
        return prop;
    }

    /**
    * Assert select(lambda xs . M, N1,.., Nk) -> M[N1/x1, ..., Nk/xk]
    */
    bool solver::assert_select_lambda_axiom(app* select, expr* lambda) {
        ++m_stats.m_num_select_lambda_axiom;
        SASSERT(is_lambda(lambda));
        SASSERT(a.is_select(select));
        SASSERT(lambda->get_sort() == select->get_arg(0)->get_sort());
        ptr_vector<expr> args(select->get_num_args(), select->get_args());
        args[0] = lambda;
        expr_ref alpha(a.mk_select(args), m);
        expr_ref beta(alpha);
        rewrite(beta);
        TRACE("array", tout << alpha << " == " << beta << "\n";);
        return ctx.propagate(e_internalize(alpha), e_internalize(beta), array_axiom());
    }

    /**
       \brief assert n1 = n2 => forall vars . (n1 vars) = (n2 vars)
     */
    bool solver::assert_congruent_axiom(expr* e1, expr* e2) {
        TRACE("array", tout << "congruence-axiom: " << mk_bounded_pp(e1, m) << " " << mk_bounded_pp(e2, m) << "\n";);
        ++m_stats.m_num_congruence_axiom;
        sort* srt         = e1->get_sort();
        unsigned dimension = get_array_arity(srt);
        expr_ref_vector args1(m), args2(m);
        args1.push_back(e1);
        args2.push_back(e2);
        svector<symbol> names;
        sort_ref_vector sorts(m);
        for (unsigned i = 0; i < dimension; i++) {
            sort * asrt = get_array_domain(srt, i);
            sorts.push_back(asrt);
            names.push_back(symbol(i));
            expr * k = m.mk_var(dimension - i - 1, asrt);
            args1.push_back(k);
            args2.push_back(k);            
        }
        expr * sel1 = a.mk_select(dimension+1, args1.data());
        expr * sel2 = a.mk_select(dimension+1, args2.data());
        expr * eq = m.mk_eq(sel1, sel2);
        expr_ref q(m.mk_forall(dimension, sorts.data(), names.data(), eq), m);
        rewrite(q);
        return add_clause(~eq_internalize(e1, e2), mk_literal(q));
    }

    bool solver::has_unitary_domain(app* array_term) {
        SASSERT(a.is_array(array_term));
        sort* s = array_term->get_sort();
        unsigned dim = get_array_arity(s);
        for (unsigned i = 0; i < dim; ++i) {
            sort* d = get_array_domain(s, i);
            if (d->is_infinite() || d->is_very_big() || 1 != d->get_num_elements().size())
                return false;
        }
        return true;
    }

    bool solver::has_large_domain(expr* array_term) {
        SASSERT(a.is_array(array_term));
        sort* s = array_term->get_sort();
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
            ctx.push(ast2ast_trail<sort, app>(m_sort2epsilon, s, eps));
        }
        if (!m_sort2diag.find(s, diag)) {
            diag = m.mk_fresh_func_decl("diag", 1, &s, s);
            ctx.push(ast2ast_trail<sort, func_decl>(m_sort2diag, s, diag));
        }
        return std::make_pair(eps, diag);
    }

    bool solver::add_delayed_axioms() {
        if (!get_config().m_array_delay_exp_axiom)
            return false;
        unsigned num_vars = get_num_vars();
        bool change = false;
        for (unsigned v = 0; v < num_vars; v++) {
            auto& d = get_var_data(v);
            if (!d.m_prop_upward)
                continue;
            euf::enode* n = var2enode(v);
            if (!ctx.is_relevant(n))
                continue;
            for (euf::enode* lambda : d.m_parent_lambdas)
                propagate_select_axioms(d, lambda);
            if (add_as_array_eqs(n))
                change = true;
            bool has_default = false;
            for (euf::enode* p : euf::enode_parents(n))
                has_default |= a.is_default(p->get_expr());
            if (!has_default)
                propagate_parent_default(v);      
        }

        unsigned sz = m_axiom_trail.size();
        m_delay_qhead = 0;
        
        for (; m_delay_qhead < sz; ++m_delay_qhead) 
            if (m_axiom_trail[m_delay_qhead].is_delayed() && assert_axiom(m_delay_qhead)) 
                change = true;              
        flet<bool> _enable_delay(m_enable_delay, false);
        if (unit_propagate())
            change = true;
        return change;
    }

    /**
     * For every occurrence of as-array(f) and every occurrence of f(t)
     * add equality select(as-array(f), t) = f(t)
     */
    bool solver::add_as_array_eqs(euf::enode* n) {
        func_decl* f = nullptr;
        bool change = false;
        if (!a.is_as_array(n->get_expr(), f))
            return false;
        for (unsigned i = 0; i < ctx.get_egraph().enodes_of(f).size(); ++i) {
            euf::enode* p = ctx.get_egraph().enodes_of(f)[i];
            if (!ctx.is_relevant(p))
                continue;
            expr_ref_vector select(m);
            select.push_back(n->get_expr());
            for (expr* arg : *to_app(p->get_expr()))
                select.push_back(arg);
            expr_ref _e(a.mk_select(select.size(), select.data()), m);
            euf::enode* e = e_internalize(_e);
            if (e->get_root() != p->get_root()) {
                sat::literal eq = eq_internalize(_e, p->get_expr());
                add_unit(eq);
                change = true;
            }
        }
        return change;
    }

    bool solver::add_interface_equalities() {
        sbuffer<theory_var> roots;
        collect_defaults();
        collect_shared_vars(roots);
        bool prop = false;
        for (unsigned i = roots.size(); i-- > 0; ) {
            theory_var v1 = roots[i];
            expr* e1 = var2expr(v1);
            for (unsigned j = i; j-- > 0; ) {
                theory_var v2 = roots[j];
                expr* e2 = var2expr(v2);
                if (e1->get_sort() != e2->get_sort())
                    continue;
                if (must_have_different_model_values(v1, v2)) 
                    continue;                
                if (ctx.get_egraph().are_diseq(var2enode(v1), var2enode(v2))) 
                    continue;                
                sat::literal lit = eq_internalize(e1, e2);
                ctx.mark_relevant(lit);
                if (s().value(lit) == l_undef) 
                    prop = true;
            }
        }
        return prop;
    }

    void solver::collect_shared_vars(sbuffer<theory_var>& roots) {
        ptr_buffer<euf::enode> to_unmark;
        unsigned num_vars = get_num_vars();
        for (unsigned i = 0; i < num_vars; i++) {
            euf::enode * n = var2enode(i);            
            if (!is_array(n)) 
                continue;
            CTRACE("array", !ctx.is_relevant(n), tout << "not relevant: " << ctx.bpp(n) << "\n");
            if (!ctx.is_relevant(n))
                continue;
            euf::enode * r = n->get_root();
            if (r->is_marked1()) 
                continue;            
            // arrays used as indices in other arrays have to be treated as shared issue #3532, #3529
            CTRACE("array", !ctx.is_shared(r) && !is_shared_arg(r), tout << "not shared: " << ctx.bpp(r) << "\n");
            if (ctx.is_shared(r) || is_shared_arg(r)) 
                roots.push_back(r->get_th_var(get_id()));           
            r->mark1();
            to_unmark.push_back(r);            
        }
        TRACE("array", tout << "collecting shared vars...\n"; for (auto v : roots) tout << ctx.bpp(var2enode(v)) << "\n";);
        for (auto* n : to_unmark)
            n->unmark1();
    }

    /**
    * \brief check that lambda expressions are beta redexes.
    * The array solver is not a decision procedure for lambdas that do not occur in beta 
    * redexes.
    */
    bool solver::check_lambdas() {
        unsigned num_vars = get_num_vars();
        for (unsigned i = 0; i < num_vars; i++) {
            auto* n = var2enode(i);
            if (a.is_as_array(n->get_expr()) || is_lambda(n->get_expr()))
                for (euf::enode* p : euf::enode_parents(n))
                    if (!ctx.is_beta_redex(p, n))
                        return false;
        }
        return true;
    }

    bool solver::is_shared_arg(euf::enode* r) {
        SASSERT(r->is_root());
        for (euf::enode* n : euf::enode_parents(r)) {
            expr* e = n->get_expr();
            if (a.is_select(e))
                for (unsigned i = 1; i < n->num_args(); ++i)
                    if (r == n->get_arg(i)->get_root())
                        return true;
            if (a.is_const(e))
                return true;
            if (a.is_ext(e))
                return true;
        }
            
        return false;
    }

}

