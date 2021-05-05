/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    dt_solver.h

Abstract:

    Theory plugin for altegraic datatypes

Author:

    Nikolaj Bjorner (nbjorner) 2020-09-08

--*/

#include "sat/smt/dt_solver.h"
#include "sat/smt/euf_solver.h"
#include "sat/smt/array_solver.h"

namespace euf {
    class solver;
}

namespace dt {

    solver::solver(euf::solver& ctx, theory_id id) :
        th_euf_solver(ctx, ctx.get_manager().get_family_name(id), id),
        dt(m),
        m_autil(m),
        m_find(*this),
        m_args(m)
    {}

    solver::~solver() {
        std::for_each(m_var_data.begin(), m_var_data.end(), delete_proc<var_data>());
        m_var_data.reset();
    }

    void solver::clone_var(solver& src, theory_var v) {
        enode* n = src.ctx.copy(ctx, src.var2enode(v));
        VERIFY(v == th_euf_solver::mk_var(n));
        m_var_data.push_back(alloc(var_data));
        var_data* d_dst = m_var_data[v];
        var_data* d_src = src.m_var_data[v];
        ctx.attach_th_var(n, this, v);
        if (d_src->m_constructor && !d_dst->m_constructor)
            d_dst->m_constructor = src.ctx.copy(ctx, d_src->m_constructor);
        for (auto* r : d_src->m_recognizers)
            d_dst->m_recognizers.push_back(src.ctx.copy(ctx, r));
    }

    euf::th_solver* solver::clone(euf::solver& dst_ctx) {
        auto* result = alloc(solver, dst_ctx, get_id());
        for (unsigned v = 0; v < get_num_vars(); ++v)
            result->clone_var(*this, v);
        return result;
    }

    solver::final_check_st::final_check_st(solver& s) : s(s) {
        SASSERT(s.m_to_unmark1.empty());
        SASSERT(s.m_to_unmark2.empty());
        s.m_used_eqs.reset();
        s.m_dfs.reset();
        s.m_parent.reset();
    }

    solver::final_check_st::~final_check_st() {
        s.clear_mark();
    }

    void solver::clear_mark() {
        for (enode* n : m_to_unmark1)
            n->unmark1();
        for (enode* n : m_to_unmark2)
            n->unmark2();
        m_to_unmark1.reset();
        m_to_unmark2.reset();
    }

    void solver::oc_mark_on_stack(enode* n) {
        n = n->get_root();
        n->mark1();
        m_to_unmark1.push_back(n);
    }

    void solver::oc_mark_cycle_free(enode* n) {
        n = n->get_root();
        n->mark2();
        m_to_unmark2.push_back(n);
    }

    void solver::oc_push_stack(enode* n) {
        m_dfs.push_back(std::make_pair(EXIT, n));
        m_dfs.push_back(std::make_pair(ENTER, n));
    }

    /**
       \brief Assert the axiom (antecedent => lhs = rhs)
       antecedent may be null_literal
    */
    void solver::assert_eq_axiom(enode* n1, expr* e2, literal antecedent) {
        expr* e1 = n1->get_expr();
        if (antecedent == sat::null_literal)
            add_unit(eq_internalize(e1, e2));
        else if (s().value(antecedent) == l_true) {
            euf::enode* n2 = e_internalize(e2);
            ctx.propagate(n1, n2, euf::th_explain::propagate(*this, antecedent, n1, n2));
        }
        else
            add_clause(~antecedent, eq_internalize(e1, e2));
    }

    /**
       \brief Assert the equality (= n (c (acc_1 n) ... (acc_m n))) where
       where acc_i are the accessors of constructor c.
    */
    void solver::assert_is_constructor_axiom(enode* n, func_decl* c, literal antecedent) {
        TRACE("dt", tout << mk_pp(c, m) << " " << ctx.bpp(n) << "\n";);
        m_stats.m_assert_cnstr++;
        expr* e = n->get_expr();
        SASSERT(dt.is_constructor(c));
        SASSERT(is_datatype(e));
        SASSERT(c->get_range() == e->get_sort());
        m_args.reset();
        for (func_decl* d : *dt.get_constructor_accessors(c))
            m_args.push_back(m.mk_app(d, e));
        expr_ref con(m.mk_app(c, m_args), m);
        assert_eq_axiom(n, con, antecedent);
    }

    /**
       \brief Given a constructor n := (c a_1 ... a_m) assert the axioms
       (= (acc_1 n) a_1)
       ...
       (= (acc_m n) a_m)
    */
    void solver::assert_accessor_axioms(enode* n) {        
        SASSERT(is_constructor(n));
        expr* e = n->get_expr();
        func_decl* d = n->get_decl();
        unsigned i = 0;
        for (func_decl* acc : *dt.get_constructor_accessors(d)) {
            m_stats.m_assert_accessor++;
            app_ref acc_app(m.mk_app(acc, e), m);
            assert_eq_axiom(n->get_arg(i), acc_app);
            ++i;
        }
    }

    /**
       \brief Sign a conflict for r := is_mk(a), c := mk(...), not(r),  and c == a.
    */
    void solver::sign_recognizer_conflict(enode* c, enode* r) {
        SASSERT(is_constructor(c));
        SASSERT(is_recognizer(r));
        SASSERT(dt.get_recognizer_constructor(r->get_decl()) == c->get_decl());
        SASSERT(c->get_root() == r->get_arg(0)->get_root());
        TRACE("dt", tout << ctx.bpp(c) << "\n" << ctx.bpp(r) << "\n";);
        literal l = ctx.enode2literal(r);
        SASSERT(s().value(l) == l_false);
        clear_mark();
        ctx.set_conflict(euf::th_explain::conflict(*this, ~l, c, r->get_arg(0)));
    }

    /**
       \brief Given a field update n := { r with field := v } for constructor C, assert the axioms:
       (=> (is-C r) (= (acc_j n) (acc_j r))) for acc_j != field
       (=> (is-C r) (= (field n) v))         for acc_j != field
       (=> (not (is-C r)) (= n r))
       (=> (is-C r) (is-C n))
    */
    void solver::assert_update_field_axioms(enode* n) {
        m_stats.m_assert_update_field++;
        SASSERT(is_update_field(n));
        expr* own = n->get_expr();
        expr* arg1 = n->get_arg(0)->get_expr();
        func_decl* upd = n->get_decl();
        func_decl* acc = to_func_decl(upd->get_parameter(0).get_ast());
        func_decl* con = dt.get_accessor_constructor(acc);
        func_decl* rec = dt.get_constructor_is(con);
        ptr_vector<func_decl> const& accessors = *dt.get_constructor_accessors(con);
        app_ref rec_app(m.mk_app(rec, arg1), m);
        app_ref acc_app(m);
        literal is_con = mk_literal(rec_app);
        for (func_decl* acc1 : accessors) {
            enode* arg;
            if (acc1 == acc) {
                arg = n->get_arg(1);
            }
            else {
                acc_app = m.mk_app(acc1, arg1);
                arg = e_internalize(acc_app);
            }
            app_ref acc_own(m.mk_app(acc1, own), m);
            assert_eq_axiom(arg, acc_own, is_con);
        }
        // update_field is identity if 'n' is not created by a matching constructor.        
        assert_eq_axiom(n, arg1, ~is_con);
        app_ref n_is_con(m.mk_app(rec, own), m);
        add_clause(~is_con, mk_literal(n_is_con));
    }

    euf::theory_var solver::mk_var(enode* n) {
        if (is_attached_to_var(n))
            return n->get_th_var(get_id());
        euf::theory_var r = th_euf_solver::mk_var(n);
        VERIFY(r == static_cast<theory_var>(m_find.mk_var()));
        SASSERT(r == static_cast<int>(m_var_data.size()));
        m_var_data.push_back(alloc(var_data));
        var_data* d = m_var_data[r];
        ctx.attach_th_var(n, this, r);
        if (is_constructor(n)) {
            d->m_constructor = n;
            assert_accessor_axioms(n);
        }
        else if (is_update_field(n)) 
            assert_update_field_axioms(n);        
        else if (!is_recognizer(n)) {
            sort* s = n->get_sort();
            if (dt.get_datatype_num_constructors(s) == 1)
                assert_is_constructor_axiom(n, dt.get_datatype_constructors(s)->get(0));
            else if (get_config().m_dt_lazy_splits == 0 || (get_config().m_dt_lazy_splits == 1 && !s->is_infinite()))
                mk_split(r, false);
        }
        return r;
    }


    /**
       \brief Create a new case split for v. That is, create the atom (is_mk v) and mark it as relevant.
       If first is true, it means that v does not have recognizer yet.
    */
    void solver::mk_split(theory_var v, bool is_final) {
        m_stats.m_splits++;
        v = m_find.find(v);
        enode* n = var2enode(v);
        sort* srt = n->get_sort();
        if (dt.is_enum_sort(srt)) {
            mk_enum_split(v);
            return;
        }
                    
        func_decl* non_rec_c = dt.get_non_rec_constructor(srt);
        unsigned non_rec_idx = dt.get_constructor_idx(non_rec_c);        
        var_data* d = m_var_data[v];
        enode* recognizer = d->m_recognizers.get(non_rec_idx, nullptr);
        SASSERT(!d->m_constructor);
        SASSERT(!recognizer || ctx.value(recognizer) == l_false || !is_final);
        
        TRACE("dt", tout << ctx.bpp(n) << " non_rec_c: " << non_rec_c->get_name() << " #rec: " << d->m_recognizers.size() << "\n";);

        if (!recognizer && non_rec_c->get_arity() == 0) {
            sat::literal eq = eq_internalize(n->get_expr(), m.mk_const(non_rec_c));
            s().set_phase(eq);
            if (s().value(eq) == l_false)
                mk_enum_split(v);
        }
        else if (!recognizer) 
            mk_recognizer_constructor_literal(non_rec_c, n);        
        else if (ctx.value(recognizer) == l_false) 
            mk_enum_split(v);
    }

    sat::literal solver::mk_recognizer_constructor_literal(func_decl* c, euf::enode* n) {
        func_decl* r = dt.get_constructor_is(c);
        app_ref r_app(m.mk_app(r, n->get_expr()), m);
        sat::literal lit = mk_literal(r_app);
        s().set_phase(lit);
        return lit;
    }

    void solver::mk_enum_split(theory_var v) {
        enode* n = var2enode(v);
        var_data* d = m_var_data[v];
        sort* srt = n->get_sort();
        auto const& constructors = *dt.get_datatype_constructors(srt);
        unsigned sz = constructors.size();
        int start = s().rand()();
        m_lits.reset();
        sat::literal lit;
        for (unsigned i = 0; i < sz; ++i) {
            unsigned j = (i + start) % sz;
            func_decl* c = constructors[j];
            if (c->get_arity() > 0) {
                enode* curr = d->m_recognizers.get(j, nullptr);
                if (curr && ctx.value(curr) != l_false)
                    return;
                lit = mk_recognizer_constructor_literal(c, n);
                if (!curr)                     
                    return;               
                if (s().value(lit) != l_false)
                    return;
                m_lits.push_back(~lit);
            }
            else {
                lit = eq_internalize(n->get_expr(), m.mk_const(c));
                switch (s().value(lit)) {
                case l_undef:
                    s().set_phase(lit);
                    return;
                case l_true:
                    return;
                case l_false:
                    m_lits.push_back(~lit);
                    break;
                }
            }
        }
        ctx.set_conflict(euf::th_explain::conflict(*this, m_lits));
    }

    /**
     * Remark: If s is an infinite sort, then it is not necessary to create
     * a theory variable. 
     * 
     * Actually, when the logical context has quantifiers, it is better to 
     * disable this optimization.
     * Example:
     *
     *   (forall (l list) (a Int) (= (len (cons a l)) (+ (len l) 1)))
     *   (assert (> (len a) 1)
     *   
     * If the theory variable is not created for 'a', then a wrong model will be generated.
     * 
     */
    void solver::apply_sort_cnstr(enode* n, sort* s) {
        TRACE("dt", tout << "apply_sort_cnstr: #" << ctx.bpp(n) << "\n";);
        force_push();
        if (!is_attached_to_var(n))
            mk_var(n);        
    }

    void solver::new_eq_eh(euf::th_eq const& eq) {
        force_push();
        m_find.merge(eq.v1(), eq.v2());
    }

    void solver::asserted(literal lit) {
        force_push();
        enode* n = bool_var2enode(lit.var());
        if (!is_recognizer(n))
            return;
        TRACE("dt", tout << "assigning recognizer: #" << n->get_expr_id() << " " << ctx.bpp(n) << "\n";);
        SASSERT(n->num_args() == 1);
        enode* arg = n->get_arg(0);
        theory_var tv = arg->get_th_var(get_id());
        tv = m_find.find(tv);
        var_data* d = m_var_data[tv];
        func_decl* r = n->get_decl();
        func_decl* c = dt.get_recognizer_constructor(r);
        if (!lit.sign()) {
            SASSERT(tv != euf::null_theory_var);
            if (d->m_constructor && d->m_constructor->get_decl() == c)
                return; // do nothing
            assert_is_constructor_axiom(arg, c, lit);
        }
        else if (d->m_constructor == nullptr)                  // make sure a constructor is attached 
            propagate_recognizer(tv, n);        
        else if (d->m_constructor->get_decl() == c)             // conflict
            sign_recognizer_conflict(d->m_constructor, n);
    }

    void solver::add_recognizer(theory_var v, enode* recognizer) {
        TRACE("dt", tout << "add recognizer " << v << " " << mk_pp(recognizer->get_expr(), m) << "\n";);
        v = m_find.find(v);
        var_data* d = m_var_data[v];
        sort* s = recognizer->get_decl()->get_domain(0);
        SASSERT(is_recognizer(recognizer));
        SASSERT(dt.is_datatype(s));
        if (d->m_recognizers.empty())
            d->m_recognizers.resize(dt.get_datatype_num_constructors(s), nullptr);

        SASSERT(d->m_recognizers.size() == dt.get_datatype_num_constructors(s));
        unsigned c_idx = dt.get_recognizer_constructor_idx(recognizer->get_decl());
        if (d->m_recognizers[c_idx])
            return;

        lbool val = ctx.value(recognizer);
        TRACE("dt", tout << "adding recognizer to v" << v << " rec: #" << recognizer->get_expr_id() << " val: " << val << "\n";);

        // do nothing... 
        // If recognizer assignment was already processed, then
        // d->m_constructor is already set.
        // Otherwise, it will be set when asserted is invoked.
        if (val == l_true)
            return;

        if (val == l_false && d->m_constructor) {
            // conflict
            if (d->m_constructor->get_decl() == dt.get_recognizer_constructor(recognizer->get_decl()))
                sign_recognizer_conflict(d->m_constructor, recognizer);
            return;
        }
        SASSERT(val == l_undef || (val == l_false && !d->m_constructor));
        ctx.push(set_vector_idx_trail<enode>(d->m_recognizers, c_idx));
        d->m_recognizers[c_idx] = recognizer;
        if (val == l_false)
            propagate_recognizer(v, recognizer);
    }

    /**
       \brief Propagate a recognizer assigned to false.
    */
    void solver::propagate_recognizer(theory_var v, enode* recognizer) {
        SASSERT(is_recognizer(recognizer));
        SASSERT(static_cast<int>(m_find.find(v)) == v);
        SASSERT(ctx.value(recognizer) == l_false);
        unsigned num_unassigned = 0;
        unsigned unassigned_idx = UINT_MAX;
        enode* n = var2enode(v);
        sort* srt = n->get_sort();
        var_data* d = m_var_data[v];
        if (d->m_recognizers.empty()) {
            add_recognizer(v, recognizer);
            return;
        }

        CTRACE("dt", d->m_recognizers.empty(), ctx.display(tout););
        SASSERT(!d->m_recognizers.empty());
        m_lits.reset();
        enode_pair_vector eqs;
        unsigned idx = 0;
        for (enode* r : d->m_recognizers) {
            if (r && ctx.value(r) == l_true)
                return; // nothing to be propagated
            if (r && ctx.value(r) == l_false) {
                SASSERT(r->num_args() == 1);
                m_lits.push_back(~ctx.enode2literal(r));
                if (n != r->get_arg(0)) {
                    // Argument of the current recognizer is not necessarily equal to n.
                    // This can happen when n and r->get_arg(0) are in the same equivalence class.
                    // We must add equality as an assumption to the conflict or propagation
                    SASSERT(n->get_root() == r->get_arg(0)->get_root());
                    eqs.push_back(euf::enode_pair(n, r->get_arg(0)));
                }
            }
            else {
                if (num_unassigned == 0)
                    unassigned_idx = idx;
                ++num_unassigned;
            }
            ++idx;
        }
        TRACE("dt", tout << "propagate " << num_unassigned << " eqs: " << eqs.size() << "\n";);
        if (num_unassigned == 0)
            ctx.set_conflict(euf::th_explain::conflict(*this, m_lits, eqs));
        else if (num_unassigned == 1) {
            // propagate remaining recognizer
            SASSERT(!m_lits.empty());
            enode* r = d->m_recognizers[unassigned_idx];
            literal consequent;
            if (r)
                consequent = ctx.enode2literal(r);
            else {
                func_decl* con = (*dt.get_datatype_constructors(srt))[unassigned_idx];
                func_decl* rec = dt.get_constructor_is(con);
                app_ref rec_app(m.mk_app(rec, n->get_expr()), m);
                consequent = mk_literal(rec_app);
            }
            ctx.propagate(consequent, euf::th_explain::propagate(*this, m_lits, eqs, consequent));
        }
        else if (get_config().m_dt_lazy_splits == 0 || (!srt->is_infinite() && get_config().m_dt_lazy_splits == 1))
            // there are more than 2 unassigned recognizers...
            // if eager splits are enabled... create new case split            
            mk_split(v, false);
    }

    void solver::merge_eh(theory_var v1, theory_var v2, theory_var, theory_var) {
        // v1 is the new root
        SASSERT(v1 == static_cast<int>(m_find.find(v1)));
        var_data* d1 = m_var_data[v1];
        var_data* d2 = m_var_data[v2];
        auto* con1 = d1->m_constructor;
        auto* con2 = d2->m_constructor;
        TRACE("dt", tout << "merging v" << v1 << " v" << v2 << "\n" << ctx.bpp(var2enode(v1)) << " == " << ctx.bpp(var2enode(v2)) << " " << ctx.bpp(con1) << " " << ctx.bpp(con2) << "\n";);
        if (con1 && con2 && con1->get_decl() != con2->get_decl())
            ctx.set_conflict(euf::th_explain::conflict(*this, con1, con2));
        else if (con2 && !con1) {
            ctx.push(set_ptr_trail<enode>(d1->m_constructor));
            // check whether there is a recognizer in d1 that conflicts with con2;
            if (!d1->m_recognizers.empty()) {
                unsigned c_idx = dt.get_constructor_idx(con2->get_decl());
                enode* recognizer = d1->m_recognizers[c_idx];
                if (recognizer && ctx.value(recognizer) == l_false) {
                    sign_recognizer_conflict(con2, recognizer);
                    return;
                }
            }
            d1->m_constructor = con2;
        }
        for (enode* e : d2->m_recognizers)
            if (e)
                add_recognizer(v1, e);
    }

    ptr_vector<euf::enode> const& solver::get_array_args(enode* n) {
        m_array_args.reset();
        array::solver* th = dynamic_cast<array::solver*>(ctx.fid2solver(m_autil.get_family_id()));
        for (enode* p : th->parent_selects(n))
            m_array_args.push_back(p);
        app_ref def(m_autil.mk_default(n->get_expr()), m);
        m_array_args.push_back(ctx.get_enode(def));
        return m_array_args;
    }

    // Assuming `app` is equal to a constructor term, return the constructor enode
    inline euf::enode* solver::oc_get_cstor(enode* app) {
        theory_var v = app->get_root()->get_th_var(get_id());
        SASSERT(v != euf::null_theory_var);
        v = m_find.find(v);
        var_data* d = m_var_data[v];
        SASSERT(d->m_constructor);
        return d->m_constructor;
    }

    void solver::explain_is_child(enode* parent, enode* child) {
        enode* parentc = oc_get_cstor(parent);
        if (parent != parentc)
            m_used_eqs.push_back(enode_pair(parent, parentc));

        // collect equalities on all children that may have been used.
        bool found = false;
        auto add = [&](enode* arg) {
            if (arg->get_root() == child->get_root()) {
                if (arg != child)
                    m_used_eqs.push_back(enode_pair(arg, child));
                found = true;
            }
        };
        for (enode* arg : euf::enode_args(parentc)) {
            add(arg);
            sort* s = arg->get_sort();
            if (m_autil.is_array(s) && dt.is_datatype(get_array_range(s)))
                for (enode* aarg : get_array_args(arg))
                    add(aarg);
        }
        VERIFY(found);
    }

    // explain the cycle root -> ... -> app -> root
    void solver::occurs_check_explain(enode* app, enode* root) {
        TRACE("dt", tout << "occurs_check_explain " << ctx.bpp(app) << " <-> " << ctx.bpp(root) << "\n";);

        // first: explain that root=v, given that app=cstor(...,v,...)

        explain_is_child(app, root);

        // now explain app=cstor(..,v,..) where v=root, and recurse with parent of app
        while (app->get_root() != root->get_root()) {
            enode* parent_app = m_parent[app->get_root()];
            explain_is_child(parent_app, app);
            SASSERT(is_constructor(parent_app));
            app = parent_app;
        }

        SASSERT(app->get_root() == root->get_root());
        if (app != root)
            m_used_eqs.push_back(enode_pair(app, root));

        TRACE("dt",
            tout << "occurs_check\n"; for (enode_pair const& p : m_used_eqs) tout << ctx.bpp(p.first) << " - " << ctx.bpp(p.second) << " ";);
    }

    // start exploring subgraph below `app`
    bool solver::occurs_check_enter(enode* app) {
        app = app->get_root();
        theory_var v = app->get_th_var(get_id());
        if (v == euf::null_theory_var)
            return false;
        v = m_find.find(v);
        var_data* d = m_var_data[v];
        if (!d->m_constructor)
            return false;
        enode* parent = d->m_constructor;
        oc_mark_on_stack(parent);
        for (enode* arg : euf::enode_args(parent)) {
            if (oc_cycle_free(arg))
                continue;
            if (oc_on_stack(arg)) {
                // arg was explored before app, and is still on the stack: cycle
                occurs_check_explain(parent, arg);
                return true;
            }
            // explore `arg` (with parent)
            expr* earg = arg->get_expr();
            sort* s = earg->get_sort();
            if (dt.is_datatype(s)) {
                m_parent.insert(arg->get_root(), parent);
                oc_push_stack(arg);
            }
            else if (m_autil.is_array(s) && dt.is_datatype(get_array_range(s))) {
                for (enode* aarg : get_array_args(arg)) {
                    if (oc_cycle_free(aarg))
                        continue;
                    if (oc_on_stack(aarg)) {
                        occurs_check_explain(parent, aarg);
                        return true;
                    }
                    if (is_datatype(aarg)) {
                        m_parent.insert(aarg->get_root(), parent);
                        oc_push_stack(aarg);
                    }
                }
            }
        }
        return false;
    }

    /**
       \brief Check if n can be reached starting from n and following equalities and constructors.
       For example, occur_check(a1) returns true in the following set of equalities:
       a1 = cons(v1, a2)
       a2 = cons(v2, a3)
       a3 = cons(v3, a1)
    */
    bool solver::occurs_check(enode* n) {
        TRACE("dt_verbose", tout << "occurs check: " << ctx.bpp(n) << "\n";);
        m_stats.m_occurs_check++;

        bool res = false;
        oc_push_stack(n);

        // DFS traversal from `n`. Look at top element and explore it.
        while (!res && !m_dfs.empty()) {
            stack_op op = m_dfs.back().first;
            enode* app = m_dfs.back().second;
            m_dfs.pop_back();

            if (oc_cycle_free(app))
                continue;

            TRACE("dt_verbose", tout << "occurs check loop: " << ctx.bpp(app) << (op == ENTER ? " enter" : " exit") << "\n";);

            switch (op) {
            case ENTER:
                res = occurs_check_enter(app);
                break;

            case EXIT:
                oc_mark_cycle_free(app);
                break;
            }
        }

        if (res) {
            clear_mark();
            ctx.set_conflict(euf::th_explain::conflict(*this, m_used_eqs));
            TRACE("dt", tout << "occurs check conflict: " << ctx.bpp(n) << "\n";);
        }
        return res;
    }

    sat::check_result solver::check() {
        force_push();
        int num_vars = get_num_vars();
        sat::check_result r = sat::check_result::CR_DONE;
        final_check_st _guard(*this);
        int start = s().rand()();
        for (int i = 0; i < num_vars; i++) {
            theory_var v = (i + start) % num_vars;
            if (v != static_cast<int>(m_find.find(v)))
                continue;
            enode* node = var2enode(v);
            if (!is_datatype(node))
                continue;
            if (dt.is_recursive(node->get_sort()) && !oc_cycle_free(node) && occurs_check(node))
                return sat::check_result::CR_CONTINUE;
            if (get_config().m_dt_lazy_splits == 0)
                continue;
            if (m_var_data[v]->m_constructor)
                continue;
            clear_mark();
            mk_split(v, true);
            r = sat::check_result::CR_CONTINUE;
        }
        return r;
    }

    void solver::pop_core(unsigned num_scopes) {
        th_euf_solver::pop_core(num_scopes);
        std::for_each(m_var_data.begin() + get_num_vars(), m_var_data.end(), delete_proc<var_data>());
        m_var_data.shrink(get_num_vars());
        SASSERT(m_find.get_num_vars() == m_var_data.size());
        SASSERT(m_find.get_num_vars() == get_num_vars());
    }

    void solver::get_antecedents(literal l, sat::ext_justification_idx idx, literal_vector& r, bool probing) {
        auto& jst = euf::th_explain::from_index(idx);
        ctx.get_antecedents(l, jst, r, probing);
    }

    void solver::add_value(euf::enode* n, model& mdl, expr_ref_vector& values) {
        theory_var v = n->get_th_var(get_id());
        if (v == euf::null_theory_var) {
            values.set(n->get_root_id(), mdl.get_fresh_value(n->get_sort()));
            return;
        }
        v = m_find.find(v);
        SASSERT(v != euf::null_theory_var);
        enode* con = m_var_data[v]->m_constructor;
        func_decl* c_decl = con->get_decl();
        m_args.reset();
        for (enode* arg : euf::enode_args(con))
            m_args.push_back(values.get(arg->get_root_id()));
        values.set(n->get_root_id(), m.mk_app(c_decl, m_args));
    }

    bool solver::add_dep(euf::enode* n, top_sort<euf::enode>& dep) {
        if (!is_datatype(n->get_expr()))
            return false;
        theory_var v = n->get_th_var(get_id());
        if (v == euf::null_theory_var) 
            return false;
        euf::enode* con = m_var_data[m_find.find(v)]->m_constructor;
        if (con->num_args() == 0)
            dep.insert(n, nullptr);
        for (enode* arg : euf::enode_args(con))
            dep.add(n, arg->get_root());
        return true;
    }

    bool solver::include_func_interp(func_decl* f) const {
        if (!dt.is_accessor(f))
            return false;
        func_decl* con = dt.get_accessor_constructor(f);
        for (enode* app : ctx.get_egraph().enodes_of(f)) {
            enode* arg = app->get_arg(0)->get_root();
            if (is_constructor(arg) && arg->get_decl() != con) 
                return true;
        }
        return false; 
    }


    sat::literal solver::internalize(expr* e, bool sign, bool root, bool redundant) {
        if (!visit_rec(m, e, sign, root, redundant)) 
            return sat::null_literal;        
        auto lit = ctx.expr2literal(e);
        if (sign)
            lit.neg();
        return lit;
    }

    void solver::internalize(expr* e, bool redundant) {
        visit_rec(m, e, false, false, redundant);
    }

    bool solver::visit(expr* e) {
        if (visited(e))
            return true;
        if (!is_app(e) || to_app(e)->get_family_id() != get_id()) {
            ctx.internalize(e, m_is_redundant);
            if (is_datatype(e))
                mk_var(expr2enode(e));
            return true;
        }
        m_stack.push_back(sat::eframe(e));
        return false;
    }

    bool solver::visited(expr* e) {
        euf::enode* n = expr2enode(e);
        return n && n->is_attached_to(get_id());
    }

    bool solver::post_visit(expr* term, bool sign, bool root) {
        euf::enode* n = expr2enode(term);
        SASSERT(!n || !n->is_attached_to(get_id()));
        if (!n)
            n = mk_enode(term);
        SASSERT(!n->is_attached_to(get_id()));
        if (is_constructor(term) || is_update_field(term)) {
            for (enode* arg : euf::enode_args(n)) {
                sort* s = arg->get_sort();
                if (dt.is_datatype(s))
                    mk_var(arg);
                else if (m_autil.is_array(s) && dt.is_datatype(get_array_range(s))) {
                    app_ref def(m_autil.mk_default(arg->get_expr()), m);
                    mk_var(e_internalize(def));
                }
            }
            mk_var(n);
        }
        else if (is_recognizer(term)) {
            mk_var(n);
            enode* arg = n->get_arg(0);
            theory_var v = mk_var(arg);
            add_recognizer(v, n);
        }
        else {
            SASSERT(is_accessor(term));
            SASSERT(n->num_args() == 1);
            mk_var(n->get_arg(0));
            if (is_datatype(n))
                mk_var(n);
        }

        return true;
    }

    void solver::collect_statistics(::statistics& st) const {
        st.update("datatype occurs check", m_stats.m_occurs_check);
        st.update("datatype splits", m_stats.m_splits);
        st.update("datatype constructor ax", m_stats.m_assert_cnstr);
        st.update("datatype accessor ax", m_stats.m_assert_accessor);
        st.update("datatype update ax", m_stats.m_assert_update_field);
    }

    std::ostream& solver::display(std::ostream& out) const {
        unsigned num_vars = get_num_vars();
        if (num_vars > 0)
            out << "Theory datatype:\n";
        for (unsigned v = 0; v < num_vars; v++)
            display_var(out, v);
        return out;
    }

    void solver::display_var(std::ostream& out, theory_var v) const {
        var_data* d = m_var_data[v];
        out << "v" << v << " #" << var2expr(v)->get_id() << " -> v" << m_find.find(v) << " ";
        if (d->m_constructor)
            out << ctx.bpp(d->m_constructor);
        else
            out << "(null)";
        out << "\n";
    }
}
