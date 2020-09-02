/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    euf_model.cpp

Abstract:

    Model building for EUF solver plugin.

Author:

    Nikolaj Bjorner (nbjorner) 2020-08-25

--*/

#include "ast/ast_pp.h"
#include "sat/smt/euf_solver.h"
#include "model/value_factory.h"

namespace euf {

    void solver::update_model(model_ref& mdl) {
        deps_t deps;
        expr_ref_vector values(m);
        collect_dependencies(deps);
        deps.topological_sort();
        dependencies2values(deps, values, mdl);
        values2model(deps, values, mdl);
    }

    bool solver::include_func_interp(func_decl* f) {
        if (f->is_skolem())
            return false;
        if (f->get_family_id() == null_family_id)
            return true;
        if (f->get_family_id() == m.get_basic_family_id())
            return false;
        euf::th_model_builder* mb = get_solver(f);
        return mb && mb->include_func_interp(f);
    }

    void solver::collect_dependencies(deps_t& deps) {
        for (enode* n : m_egraph.nodes()) {
            if (n->num_args() == 0) {
                deps.insert(n, nullptr);
                continue;
            }
            auto* mb = get_solver(n->get_owner());
            if (mb)
                mb->add_dep(n, deps);
            else
                deps.insert(n, nullptr);
        }
    }

    void solver::dependencies2values(deps_t& deps, expr_ref_vector& values, model_ref const& mdl) {
        user_sort_factory user_sort(m);
        for (enode* n : deps.top_sorted()) {
            unsigned id = n->get_root_id();
            if (values.get(id, nullptr))
                continue;
            expr* e = n->get_owner();
            values.reserve(id + 1);
            if (m.is_bool(e) && is_uninterp_const(e) && mdl->get_const_interp(to_app(e)->get_decl())) {
                values.set(id, mdl->get_const_interp(to_app(e)->get_decl()));
                continue;
            }
            // model of s() must have been fixed.
            if (m.is_bool(e)) {
                if (m.is_true(e)) {
                    values.set(id, m.mk_true());
                    continue;
                }
                if (m.is_false(e)) {
                    values.set(id, m.mk_false());
                    continue;
                }
                if (is_app(e) && to_app(e)->get_family_id() == m.get_basic_family_id())
                    continue;
                sat::bool_var v = m_expr2var.to_bool_var(e);
                SASSERT(v != sat::null_bool_var);
                switch (s().value(v)) {
                case l_true:
                    values.set(id, m.mk_true());
                    break;
                case l_false:
                    values.set(id, m.mk_false());
                    break;
                default:
                    break;
                }
                continue;
            }
            auto* mb = get_solver(e);
            if (mb) 
                mb->add_value(n, values);
            else if (m.is_uninterp(m.get_sort(e))) {
                expr* v = user_sort.get_fresh_value(m.get_sort(e));
                values.set(id, v);
            }
            else {
                IF_VERBOSE(1, verbose_stream() << "no model values created for " << mk_pp(e, m) << "\n");
            }                
        }
    }

    void solver::values2model(deps_t const& deps, expr_ref_vector const& values, model_ref& mdl) {
        ptr_vector<expr> args;
        for (enode* n : deps.top_sorted()) {
            expr* e = n->get_owner();
            if (!is_app(e))
                continue;
            app* a = to_app(e);
            func_decl* f = a->get_decl();            
            if (!include_func_interp(f))
                continue;
            if (m.is_bool(e) && is_uninterp_const(e) && mdl->get_const_interp(f))
                continue;
            expr* v = values.get(n->get_root_id());
            unsigned arity = f->get_arity();
            if (arity == 0) 
                mdl->register_decl(f, v);
            else {
                auto* fi = mdl->get_func_interp(f);
                if (!fi) {                    
                    fi = alloc(func_interp, m, arity);
                    mdl->register_decl(f, fi);
                }
                args.reset();
                for (enode* arg : enode_args(n)) 
                    args.push_back(values.get(arg->get_root_id()));
                if (!fi->get_entry(args.c_ptr()))
                    fi->insert_new_entry(args.c_ptr(), v);
            }
        }
    }

    void solver::register_macros(model& mdl) {
        // TODO
    }

}
