/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    array_model.cpp

Abstract:

    Theory plugin for arrays

Author:

    Nikolaj Bjorner (nbjorner) 2020-09-08

--*/

#include "ast/ast_ll_pp.h"
#include "model/array_factory.h"
#include "sat/smt/array_solver.h"
#include "sat/smt/euf_solver.h"

namespace array {
    
    
    void solver::add_dep(euf::enode* n, top_sort<euf::enode>& dep) { 
        if (!a.is_array(n->get_expr())) {
            dep.insert(n, nullptr);
            return;
        }
        for (euf::enode* p : euf::enode_parents(n)) {
            if (!a.is_select(p->get_expr()))
                continue;
            dep.add(n, p);
            for (unsigned i = 1; i < p->num_args(); ++i)
                dep.add(n, p->get_arg(i));
        }
        for (euf::enode* k : euf::enode_class(n)) 
            if (a.is_const(k->get_expr()))
                dep.add(n, k);    
            else if (a.is_default(k->get_expr()))
                dep.add(n, k);
    }


    void solver::add_value(euf::enode* n, model& mdl, expr_ref_vector& values) {
        SASSERT(a.is_array(n->get_expr()));
        ptr_vector<expr> args;
        sort* srt = m.get_sort(n->get_expr());
        unsigned arity = get_array_arity(srt);
        func_decl * f    = mk_aux_decl_for_array_sort(m, srt);
        func_interp * fi = alloc(func_interp, m, arity);
        mdl.register_decl(f, fi);

        for (euf::enode* p : euf::enode_parents(n)) {
            if (!a.is_select(p->get_expr()))
                continue;
            args.reset();
            for (unsigned i = 1; i < p->num_args(); ++i) 
                args.push_back(values.get(p->get_arg(i)->get_root_id()));
            expr* value = values.get(p->get_root_id());
            fi->insert_entry(args.c_ptr(), value);
        }
        if (!fi->get_else()) 
            for (euf::enode* k : euf::enode_class(n))             
                if (a.is_const(k->get_expr())) 
                    fi->set_else(k->get_arg(0)->get_root()->get_expr());
        if (!fi->get_else())
            for (euf::enode* k : euf::enode_parents(n))             
                if (a.is_default(k->get_expr())) 
                    fi->set_else(k->get_root()->get_expr());
        
        parameter p(f);
        values.set(n->get_root_id(), m.mk_app(get_id(), OP_AS_ARRAY, 1, &p));
    }

}
