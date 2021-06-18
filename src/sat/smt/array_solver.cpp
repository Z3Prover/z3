/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    array_solver.cpp

Abstract:

    Theory plugin for arrays

Author:

    Nikolaj Bjorner (nbjorner) 2020-09-08

Notes:

A node n has attribtes:

    parent_selects:   { A[i] | A ~ n }
    parent_lambdas:     { store(A,i,v) | A ~ n } u { map(f, .., A, ..) | A ~ n }
    lambdas:            { const(v) | const(v) ~ n }
                      u { map(f,..) | map(f,..) ~ n }
                      u { store(A,i,v) | store(A,i,v) ~ n }
                      u { as-array(f) | as-array(f) ~ n }

The attributes are used for propagation.
When n1 is merged with n2, and n1 is the new root, the attributes from n2 are added to n1.
The merge also looks for new redexes.

Let A[j] in parent_selects(n2) :

        lambda in parent_lambdas(n1)
    -------------------------------
     lambda[j] = beta-reduce(lambda[j])

            lambda in lambdas(n1)
    -------------------------------
     lambda[j] = beta-reduce(lambda[j])

Beta reduction rules are:
      beta-reduce(store(A,j,v)[i]) = if(i = j, v, A[j])
      beta-reduce(map(f,A,B)[i]) = f(A[i],B[i])
      beta-reduce(as-array(f)[i]) = f(i)
      beta-reduce(const(v)[i]) = v
      beta-reduce((lambda x M[x])[i]) = M[i]

For enforcing
      store(A,j,v)[i] = beta-reduce(store(A,j,v)[i])

      only the following axiom is instantiated:
      - i = j or store(A,j,v)[i] = A[i]

The other required axiom, store(A,j,v)[j] = v
is added eagerly whenever store(A,j,v) is created.

Current setup: to enforce extensionality on lambdas, 
also currently, as a base-line it is eager:

        A ~ B, A = lambda x. M[x]
    -------------------------------
    A = B => forall i . M[i] = B[i]

A hypothetical refinement could use some limited HO pattern unification steps.
For example
    lambda x y z . Y z y x = lambda x y z . X x z y
-> Y = lambda x y z . X ....

--*/

#include "ast/ast_ll_pp.h"
#include "sat/smt/array_solver.h"
#include "sat/smt/euf_solver.h"

namespace array {

    solver::solver(euf::solver& ctx, theory_id id) :
        th_euf_solver(ctx, symbol("array"), id),
        a(m),
        m_sort2epsilon(m),
        m_sort2diag(m),
        m_find(*this),
        m_hash(*this),
        m_eq(*this),
        m_axioms(DEFAULT_HASHTABLE_INITIAL_CAPACITY, m_hash, m_eq)
    {
        m_constraint = alloc(sat::constraint_base);
        m_constraint->initialize(m_constraint.get(), this);
    }

    solver::~solver() {}

    sat::check_result solver::check() {
        force_push();
        // flet<bool> _is_redundant(m_is_redundant, true);
        bool turn[2] = { false, false };
        turn[s().rand()(2)] = true;
        for (unsigned idx = 0; idx < 2; ++idx) {
            if (turn[idx] && add_delayed_axioms())
                return sat::check_result::CR_CONTINUE;
            else if (!turn[idx] && add_interface_equalities())
                return sat::check_result::CR_CONTINUE;
        }
        if (m_delay_qhead < m_axiom_trail.size()) 
            return sat::check_result::CR_CONTINUE;
            
        // validate_check();
        return sat::check_result::CR_DONE;
    }

    void solver::pop_core(unsigned n) {
        th_euf_solver::pop_core(n);
        m_var_data.resize(get_num_vars());
    }

    euf::th_solver* solver::clone(euf::solver& dst_ctx) {
        auto* result = alloc(solver, dst_ctx, get_id());
        for (unsigned i = 0; i < get_num_vars(); ++i)          
            result->mk_var(ctx.copy(dst_ctx, var2enode(i)));        
        return result;
    }

    void solver::new_eq_eh(euf::th_eq const& eq) {
        force_push();
        m_find.merge(eq.v1(), eq.v2());
    }

    void solver::new_diseq_eh(euf::th_eq const& eq) {
        force_push();
        euf::enode* n1 = var2enode(eq.v1());
        euf::enode* n2 = var2enode(eq.v2());
        if (is_array(n1))
            push_axiom(extensionality_axiom(n1, n2));
    }

    bool solver::unit_propagate() {
        if (m_qhead == m_axiom_trail.size())
            return false;
        force_push();
        bool prop = false;
        ctx.push(value_trail<unsigned>(m_qhead));
        for (; m_qhead < m_axiom_trail.size() && !s().inconsistent(); ++m_qhead)
            if (propagate_axiom(m_qhead))
                prop = true;
        return prop;
    }

    void solver::merge_eh(theory_var v1, theory_var v2, theory_var, theory_var) {
        euf::enode* n1 = var2enode(v1);
        euf::enode* n2 = var2enode(v2);
        TRACE("array", tout << "merge: " << ctx.bpp(n1) << " == " << ctx.bpp(n2) << "\n";);
        SASSERT(n1->get_root() == n2->get_root());
        SASSERT(v1 == find(v1));
        expr* e1 = n1->get_expr();
        expr* e2 = n2->get_expr();
        auto& d1 = get_var_data(v1);
        auto& d2 = get_var_data(v2);
        if (d2.m_prop_upward && !d1.m_prop_upward)
            set_prop_upward(v1);
        for (euf::enode* lambda : d2.m_lambdas)
            add_lambda(v1, lambda);
        for (euf::enode* lambda : d2.m_parent_lambdas)
            add_parent_lambda(v1, lambda);
        for (euf::enode* select : d2.m_parent_selects)
            add_parent_select(v1, select);
        if (is_lambda(e1) || is_lambda(e2))
            push_axiom(congruence_axiom(n1, n2));
    }

    void solver::add_parent_select(theory_var v_child, euf::enode* select) {
        SASSERT(a.is_select(select->get_expr()));
        SASSERT(select->get_arg(0)->get_sort() == var2expr(v_child)->get_sort());
        v_child = find(v_child);
        ctx.push_vec(get_var_data(v_child).m_parent_selects, select);
        euf::enode* child = var2enode(v_child);
        TRACE("array", tout << "v" << v_child << " - " << ctx.bpp(select) << " " << ctx.bpp(child) << " prop: " << should_prop_upward(get_var_data(v_child)) << "\n";);
        if (can_beta_reduce(child)) 
            push_axiom(select_axiom(select, child));
    }

    void solver::add_lambda(theory_var v, euf::enode* lambda) {
        SASSERT(can_beta_reduce(lambda));
        auto& d = get_var_data(find(v));
        if (should_set_prop_upward(d))
            set_prop_upward(d);
        ctx.push_vec(d.m_lambdas, lambda);
        if (should_set_prop_upward(d)) {
            set_prop_upward(lambda);
            propagate_select_axioms(d, lambda);
        }
    }

    void solver::add_parent_lambda(theory_var v_child, euf::enode* lambda) {
        SASSERT(can_beta_reduce(lambda));
        auto& d = get_var_data(find(v_child));
        ctx.push_vec(d.m_parent_lambdas, lambda);
        if (should_set_prop_upward(d))
            propagate_select_axioms(d, lambda);
    }

    void solver::add_parent_default(theory_var v, euf::enode* def) {
        SASSERT(a.is_default(def->get_expr()));
        auto& d = get_var_data(find(v));
        for (euf::enode* lambda : d.m_lambdas)
            push_axiom(default_axiom(lambda));
        if (should_prop_upward(d))
            propagate_parent_default(v);
    }

    void solver::propagate_select_axioms(var_data const& d, euf::enode* lambda) {
        for (euf::enode* select : d.m_parent_selects)
            push_axiom(select_axiom(select, lambda));
    }

    void solver::propagate_parent_default(theory_var v) {
        auto& d = get_var_data(find(v));
        for (euf::enode* lambda : d.m_parent_lambdas)
            push_axiom(default_axiom(lambda));
    }

    void solver::propagate_parent_select_axioms(theory_var v) {
        v = find(v);
        expr* e = var2expr(v);
        if (!a.is_array(e))
            return;
        
        auto& d = get_var_data(v);

        for (euf::enode* lambda : d.m_parent_lambdas)
            propagate_select_axioms(d, lambda);
    }

    void solver::set_prop_upward(theory_var v) {
        auto& d = get_var_data(find(v));
        if (d.m_prop_upward)
            return;
        ctx.push(reset_flag_trail(d.m_prop_upward));
        d.m_prop_upward = true;
        if (should_prop_upward(d))
            propagate_parent_select_axioms(v);
        set_prop_upward(d);
    }

    void solver::set_prop_upward(euf::enode* n) {
        if (a.is_store(n->get_expr()))
            set_prop_upward(n->get_arg(0)->get_th_var(get_id()));
    }

    void solver::set_prop_upward(var_data& d) {
        for (auto* p : d.m_lambdas)
            set_prop_upward(p);
    }

    /**
       \brief Return the size of the equivalence class for array terms
              that can be expressed as \lambda i : Index . [.. (select a i) ..]
     */
    unsigned solver::get_lambda_equiv_size(var_data const& d) const {
        return d.m_parent_selects.size() + 2 * d.m_lambdas.size();
    }

    bool solver::should_set_prop_upward(var_data const& d) const {
        return get_config().m_array_always_prop_upward || get_lambda_equiv_size(d) >= 1;
    }

    bool solver::should_prop_upward(var_data const& d) const {
        return !get_config().m_array_delay_exp_axiom && d.m_prop_upward;
    }

    bool solver::can_beta_reduce(euf::enode* n) const {
        expr* c = n->get_expr();
        return a.is_const(c) || a.is_as_array(c) || a.is_store(c) || is_lambda(c) || a.is_map(c);
    }
}
