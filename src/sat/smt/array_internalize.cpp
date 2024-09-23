/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    array_internalize.cpp

Abstract:

    Internalize routines for arrays

Author:

    Nikolaj Bjorner (nbjorner) 2020-09-08

--*/

#include "sat/smt/array_solver.h"
#include "sat/smt/euf_solver.h"

namespace array {

    sat::literal solver::internalize(expr* e, bool sign, bool root) { 
        SASSERT(m.is_bool(e));
        if (!visit_rec(m, e, sign, root)) {
            TRACE("array", tout << mk_pp(e, m) << "\n";);
            return sat::null_literal;
        }
        auto lit = expr2literal(e);
        if (sign)
            lit.neg();
        return lit;
    }

    void solver::internalize(expr* e) {
        visit_rec(m, e, false, false);
    }

    euf::theory_var solver::mk_var(euf::enode* n) {
        theory_var r = euf::th_euf_solver::mk_var(n);
        m_find.mk_var();
        ctx.attach_th_var(n, this, r);
        m_var_data.push_back(alloc(var_data));
        return r;
    }

    void solver::ensure_var(euf::enode* n) {
        theory_var v = n->get_th_var(get_id());
        if (v == euf::null_theory_var) {
            mk_var(n);
            if (is_lambda(n->get_expr()))
                internalize_lambda_eh(n);
        }
    }

    void solver::apply_sort_cnstr(euf::enode * n, sort * s) {
        ensure_var(n);
    }

    bool solver::visited(expr* e) {
        euf::enode* n = expr2enode(e);
        return n && n->is_attached_to(get_id());        
    }

    bool solver::visit(expr* e) {
        if (visited(e))
            return true;
        if (!is_app(e) || to_app(e)->get_family_id() != get_id()) {
            ctx.internalize(e);
            euf::enode* n = expr2enode(e);
            ensure_var(n);
            return true;
        }
        m_stack.push_back(sat::eframe(e));
        return false;        
    }

    bool solver::post_visit(expr* e, bool sign, bool root) {
        euf::enode* n = expr2enode(e);
        app *a = to_app(e);
        (void)a;
        SASSERT(!n || !n->is_attached_to(get_id()));
        if (!n) 
            n = mk_enode(e, false);
        if (!n->is_attached_to(get_id())) 
            mk_var(n);
        for (auto* arg : euf::enode_args(n))
            ensure_var(arg);  
        internalize_eh(n);
        if (ctx.is_relevant(n))
            relevant_eh(n);
        return true;
    }

    void solver::internalize_lambda_eh(euf::enode* n) {
        push_axiom(default_axiom(n));
        auto& d = get_var_data(find(n));
        ctx.push_vec(d.m_lambdas, n);
    }

    void solver::internalize_eh(euf::enode* n) {
        auto k = n->get_decl()->get_decl_kind();
        switch (k) {
        case OP_STORE:          
            ctx.push_vec(get_var_data(find(n)).m_lambdas, n);
            push_axiom(store_axiom(n));
            break;
        case OP_SELECT:
            break;
        case OP_AS_ARRAY:
        case OP_CONST_ARRAY:
            internalize_lambda_eh(n);
            break;
        case OP_ARRAY_EXT:
            SASSERT(is_array(n->get_arg(0)));
            push_axiom(extensionality_axiom(n->get_arg(0), n->get_arg(1)));
            break;
        case OP_ARRAY_DEFAULT:
            add_parent_default(find(n->get_arg(0)));
            break;
        case OP_ARRAY_MAP:
        case OP_SET_UNION:
        case OP_SET_INTERSECT:
        case OP_SET_DIFFERENCE:
        case OP_SET_COMPLEMENT:
            for (auto* arg : euf::enode_args(n)) 
                add_parent_lambda(find(arg), n);
            internalize_lambda_eh(n);
            break;
        case OP_SET_SUBSET: {
            expr* x = nullptr, *y = nullptr;
            VERIFY(a.is_subset(n->get_expr(), x, y));
            expr_ref diff(a.mk_setminus(x, y), m);
            expr_ref emp(a.mk_empty_set(x->get_sort()), m);
            sat::literal eq = eq_internalize(diff, emp);
            sat::literal sub = expr2literal(n->get_expr());
            add_equiv(eq, sub);
            break;
        }            
        case OP_SET_HAS_SIZE:
        case OP_SET_CARD:
            ctx.unhandled_function(n->get_decl());
            break;
        default:
            UNREACHABLE();
            break;
        }
    }

    void solver::relevant_eh(euf::enode* n) {
        if (is_lambda(n->get_expr())) {
            set_prop_upward(find(n));
            return;
        }
        if (!is_app(n->get_expr()))
            return;
        if (n->get_decl()->get_family_id() != a.get_family_id())
            return;
        switch (n->get_decl()->get_decl_kind()) {
        case OP_STORE:
            add_parent_lambda(find(n->get_arg(0)), n);   
            break;
        case OP_SELECT:
            add_parent_select(find(n->get_arg(0)), n);
            break;
        case OP_CONST_ARRAY:
        case OP_AS_ARRAY:
            set_prop_upward(find(n));            
            propagate_parent_default(find(n));
            break;
        case OP_ARRAY_EXT:
            break;
        case OP_ARRAY_DEFAULT:
            set_prop_upward(find(n->get_arg(0)));
            break;
        case OP_ARRAY_MAP:
        case OP_SET_UNION:
        case OP_SET_INTERSECT:
        case OP_SET_DIFFERENCE:
        case OP_SET_COMPLEMENT:
            for (auto* arg : euf::enode_args(n)) 
                set_prop_upward_store(arg);
            set_prop_upward(find(n));
            break;
        case OP_SET_SUBSET:
            break;
        case OP_SET_HAS_SIZE:
        case OP_SET_CARD:
            ctx.unhandled_function(n->get_decl());
            break;
        default:
            UNREACHABLE();
            break;
        }
    }

    /**
        \brief Return true if v is shared between two different "instances" of the array theory.
        It is shared if it is used in more than one role. The possible roles are: array, index, and value.
        Example:
          (store v i j) <--- v is used as an array
          (select A v)  <--- v is used as an index
          (store A i v) <--- v is used as an value
     */
    bool solver::is_shared(theory_var v) const {
        euf::enode* n = var2enode(v);
        euf::enode* r = n->get_root();
        bool is_array = false;
        bool is_index = false;
        bool is_value = false;
        auto set_array = [&](euf::enode* arg) { if (arg->get_root() == r) is_array = true; };
        auto set_index = [&](euf::enode* arg) { if (arg->get_root() == r) is_index = true; };
        auto set_value = [&](euf::enode* arg) { if (arg->get_root() == r) is_value = true; };

        if (a.is_ext(n->get_expr()))
            return true;
        for (euf::enode* parent : euf::enode_parents(r)) {
            app* p = parent->get_app();
            unsigned num_args = parent->num_args();
            if (a.is_store(p)) {
                set_array(parent->get_arg(0));
                for (unsigned i = 1; i < num_args - 1; i++)
                    set_index(parent->get_arg(i));
                set_value(parent->get_arg(num_args - 1));
            }
            else if (a.is_select(p)) {
                set_array(parent->get_arg(0));
                for (unsigned i = 1; i < num_args - 1; i++)
                    set_index(parent->get_arg(i));
            }
            else if (a.is_const(p)) {
                set_value(parent->get_arg(0));
            }            
            if (is_array + is_index + is_value > 1)
                return true;
        }
        return false;
    }

    bool solver::is_beta_redex(euf::enode* p, euf::enode* n) const {
        if (a.is_select(p->get_expr()))
            return p->get_arg(0)->get_root() == n->get_root();
        if (a.is_map(p->get_expr()))
            return true;
        if (a.is_store(p->get_expr()))
            return true;
        return false;
    }

    func_decl_ref_vector const& solver::sort2diff(sort* s) {
        func_decl_ref_vector* result = nullptr;
        if (m_sort2diff.find(s, result))
            return *result;
        
        unsigned dimension = get_array_arity(s);
        result = alloc(func_decl_ref_vector, m);
        for (unsigned i = 0; i < dimension; ++i) 
            result->push_back(a.mk_array_ext(s, i));
        m_sort2diff.insert(s, result);
        ctx.push(insert_map<obj_map<sort, func_decl_ref_vector*>, sort*>(m_sort2diff, s));
        ctx.push(new_obj_trail<func_decl_ref_vector>(result));
        return *result;
    }

}

