/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    array_model.cpp

Abstract:

    Theory plugin for arrays

Author:

    Nikolaj Bjorner (nbjorner) 2020-09-08

--*/

#include "model/array_factory.h"
#include "sat/smt/array_solver.h"
#include "sat/smt/euf_solver.h"

namespace array {
    
    
    bool solver::add_dep(euf::enode* n, top_sort<euf::enode>& dep) { 
        if (!a.is_array(n->get_expr())) {
            dep.insert(n, nullptr);
            return true;
        }
        for (euf::enode* p : euf::enode_parents(n)) {
            if (a.is_default(p->get_expr())) {
                dep.add(n, p);
                continue;
            }
            if (!a.is_select(p->get_expr()))
                continue;
            dep.add(n, p);
            for (unsigned i = 1; i < p->num_args(); ++i)
                dep.add(n, p->get_arg(i));
        }
        for (euf::enode* k : euf::enode_class(n)) 
            if (a.is_const(k->get_expr())) 
                dep.add(n, k->get_arg(0)); 
        if (!dep.deps().contains(n))
            dep.insert(n, nullptr);
        return true;
    }


    void solver::add_value(euf::enode* n, model& mdl, expr_ref_vector& values) {
        SASSERT(a.is_array(n->get_expr()));
        ptr_vector<expr> args;
        sort* srt = n->get_sort();
        unsigned arity = get_array_arity(srt);
        func_decl * f    = mk_aux_decl_for_array_sort(m, srt);
        func_interp * fi = alloc(func_interp, m, arity);
        mdl.register_decl(f, fi);

        if (!fi->get_else())
            for (euf::enode* k : euf::enode_class(n))
                if (a.is_const(k->get_expr()))
                    fi->set_else(values.get(k->get_arg(0)->get_root_id()));

        if (!fi->get_else())
            for (euf::enode* p : euf::enode_parents(n))
                if (a.is_default(p->get_expr()))
                    fi->set_else(values.get(p->get_root_id()));
    
        if (!fi->get_else()) {
            expr* else_value = nullptr;
            unsigned max_occ_num = 0;
            obj_map<expr, unsigned> num_occ;
            for (euf::enode* p : euf::enode_parents(n)) {
                if (a.is_select(p->get_expr()) && p->get_arg(0)->get_root() == n->get_root()) {
                    expr* v = values.get(p->get_root_id());
                    if (!v)
                        continue;
                    unsigned no = 0;
                    num_occ.find(v, no);
                    ++no;
                    num_occ.insert(v, no);
                    if (no > max_occ_num) {
                        else_value = v;
                        max_occ_num = no;
                    }
                }
            }
            if (else_value)
                fi->set_else(else_value);
        }

        for (euf::enode* p : euf::enode_parents(n)) {
            if (a.is_select(p->get_expr()) && p->get_arg(0)->get_root() == n->get_root()) {
                expr* value = values.get(p->get_root_id());
                if (!value || value == fi->get_else())
                    continue;
                args.reset();
                for (unsigned i = 1; i < p->num_args(); ++i) 
                    args.push_back(values.get(p->get_arg(i)->get_root_id()));    
                fi->insert_entry(args.data(), value);
            }
        }
        
        parameter p(f);
        values.set(n->get_root_id(), m.mk_app(get_id(), OP_AS_ARRAY, 1, &p));
    }


    bool solver::have_different_model_values(theory_var v1, theory_var v2) {
        euf::enode* else1 = nullptr, * else2 = nullptr;
        euf::enode* n1 = var2enode(v1), *n2 = var2enode(v2);
        euf::enode* r1 = n1->get_root(), * r2 = n2->get_root();
        expr* e1 = n1->get_expr();
        expr* e;
        if (!a.is_array(e1))
            return true;
        auto find_else = [&](theory_var v, euf::enode* r) {
            var_data& d = get_var_data(find(v));
            for (euf::enode* c : d.m_lambdas)
                if (a.is_const(c->get_expr(), e))
                    return expr2enode(e)->get_root();
            for (euf::enode* p : euf::enode_parents(r))
                for (euf::enode* pe : euf::enode_class(p))
                    if (a.is_default(pe->get_expr()))
                        return pe->get_root();
            return (euf::enode*)nullptr;
        };
        else1 = find_else(v1, r1);
        else2 = find_else(v2, r2);
        if (else1 && else2 && else1->get_root() != else2->get_root() && has_large_domain(e1))
            return true;
        struct eq {
            solver& s;
            eq(solver& s) :s(s) {}
            bool operator()(euf::enode* n1, euf::enode* n2) const {
                SASSERT(s.a.is_select(n1->get_expr()));
                SASSERT(s.a.is_select(n2->get_expr()));
                for (unsigned i = n1->num_args(); i-- > 1; ) 
                    if (n1->get_arg(i)->get_root() != n2->get_arg(i)->get_root())
                        return false;
                return true;                
            }
        };
        struct hash {
            solver& s;
            hash(solver& s) :s(s) {}
            unsigned operator()(euf::enode* n) const {
                SASSERT(s.a.is_select(n->get_expr()));
                unsigned h = 33;
                for (unsigned i = n->num_args(); i-- > 1; )
                    h = hash_u_u(h, n->get_arg(i)->get_root_id());
                return h;
            }
        };
        eq eq_proc(*this);
        hash hash_proc(*this);
        hashtable<euf::enode*, hash, eq> table(DEFAULT_HASHTABLE_INITIAL_CAPACITY, hash_proc, eq_proc);
        euf::enode* p2 = nullptr;
        auto maps_diff = [&](euf::enode* p, euf::enode* else_, euf::enode* r) {
            return table.find(p, p2) ? p2->get_root() != r : (else_ && else_ != r);
        };
        auto table_diff = [&](euf::enode* r1, euf::enode* r2, euf::enode* else1) {
            table.reset();
            for (euf::enode* p : euf::enode_parents(r1))
                if (a.is_select(p->get_expr()) && r1 == p->get_arg(0)->get_root())
                    table.insert(p);
            for (euf::enode* p : euf::enode_parents(r2))
                if (a.is_select(p->get_expr()) && r2 == p->get_arg(0)->get_root())
                    if (maps_diff(p, else1, p->get_root()))
                        return true;
            return false;
        };
        
        return table_diff(r1, r2, else1) || table_diff(r2, r1, else2);
    }

}
