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

    sat::literal solver::internalize(expr* e, bool sign, bool root, bool redundant) { 
        SASSERT(m.is_bool(e));
        if (!visit_rec(m, e, sign, root, redundant)) {
            TRACE("array", tout << mk_pp(e, m) << "\n";);
            return sat::null_literal;
        }
        auto lit = expr2literal(e);
        if (sign)
            lit.neg();
        return lit;
    }

    void solver::internalize(expr* e, bool redundant) {
        visit_rec(m, e, false, false, redundant);
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
                internalize_lambda(n);
        }
    }

    void solver::apply_sort_cnstr(euf::enode * n, sort * s) {
        ensure_var(n);
    }

    void solver::internalize_store(euf::enode* n) {
        add_parent_lambda(n->get_arg(0)->get_th_var(get_id()), n);   
        push_axiom(store_axiom(n));
        add_lambda(n->get_th_var(get_id()), n);
        SASSERT(!get_var_data(n->get_th_var(get_id())).m_prop_upward);
    }

    void solver::internalize_map(euf::enode* n) {
        for (auto* arg : euf::enode_args(n)) {
            add_parent_lambda(arg->get_th_var(get_id()), n);
            set_prop_upward(arg);
        }
        push_axiom(default_axiom(n));
        add_lambda(n->get_th_var(get_id()), n);
        SASSERT(!get_var_data(n->get_th_var(get_id())).m_prop_upward);
    }

    void solver::internalize_lambda(euf::enode* n) {
        set_prop_upward(n);
        if (!a.is_store(n->get_expr()))
            push_axiom(default_axiom(n));
        add_lambda(n->get_th_var(get_id()), n);
    }

    void solver::internalize_select(euf::enode* n) {
        add_parent_select(n->get_arg(0)->get_th_var(get_id()), n);
    }

    void solver::internalize_ext(euf::enode* n) {
        SASSERT(is_array(n->get_arg(0)));
        push_axiom(extensionality_axiom(n->get_arg(0), n->get_arg(1)));
    }

    void solver::internalize_default(euf::enode* n) {
        add_parent_default(n->get_arg(0)->get_th_var(get_id()), n);
        set_prop_upward(n);
    }

    bool solver::visited(expr* e) {
        euf::enode* n = expr2enode(e);
        return n && n->is_attached_to(get_id());        
    }

    bool solver::visit(expr* e) {
        if (visited(e))
            return true;
        if (!is_app(e) || to_app(e)->get_family_id() != get_id()) {
            ctx.internalize(e, m_is_redundant);
            euf::enode* n = expr2enode(e);
            ensure_var(n);
            return true;
        }
        m_stack.push_back(sat::eframe(e));
        return false;        
    }

    bool solver::post_visit(expr* e, bool sign, bool root) {
        euf::enode* n = expr2enode(e);
        app* a = to_app(e);        
        SASSERT(!n || !n->is_attached_to(get_id()));
        if (!n) 
            n = mk_enode(e, false);
        SASSERT(!n->is_attached_to(get_id()));
        mk_var(n);
        for (auto* arg : euf::enode_args(n))
            ensure_var(arg);  
        switch (a->get_decl_kind()) {
        case OP_STORE:           
            internalize_store(n); 
            break;
        case OP_SELECT:          
            internalize_select(n); 
            break;
        case OP_AS_ARRAY:
        case OP_CONST_ARRAY:     
            internalize_lambda(n); 
            break;
        case OP_ARRAY_EXT:       
            internalize_ext(n); 
            break;
        case OP_ARRAY_DEFAULT:   
            internalize_default(n); 
            break;
        case OP_ARRAY_MAP:       
            internalize_map(n); 
            break;
        case OP_SET_UNION:       
        case OP_SET_INTERSECT:   
        case OP_SET_DIFFERENCE:  
        case OP_SET_COMPLEMENT:  
        case OP_SET_SUBSET:      
        case OP_SET_HAS_SIZE:    
        case OP_SET_CARD:        
            ctx.unhandled_function(a->get_decl()); 
            break;
        default:
            UNREACHABLE();
            break;            
        }
        return true;
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

