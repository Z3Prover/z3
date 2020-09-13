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
        if (!visit_rec(m, e, sign, root, redundant))
            return sat::null_literal;
        return expr2literal(e);
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
        push_axiom(default_axiom(n));
        add_lambda(n->get_th_var(get_id()), n);
    }

    void solver::internalize_select(euf::enode* n) {
        add_parent_select(n->get_arg(0)->get_th_var(get_id()), n);
    }

    void solver::internalize_ext(euf::enode* n) {
        push_axiom(extensionality_axiom(n));
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

}

