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
#include "ast/ast_ll_pp.h"
#include "sat/smt/euf_solver.h"
#include "model/value_factory.h"

namespace euf {

    void solver::update_model(model_ref& mdl) {
        for (auto* mb : m_solvers)
            mb->init_model();
        deps_t deps;
        m_values.reset();
        m_values2root.reset();
        collect_dependencies(deps);
        deps.topological_sort();
        dependencies2values(deps, mdl);
        values2model(deps, mdl);
        for (auto* mb : m_solvers)
            mb->finalize_model(*mdl);
        // validate_model(*mdl);
    }

    bool solver::include_func_interp(func_decl* f) {
        if (f->is_skolem())
            return false;
        if (f->get_family_id() == null_family_id)
            return true;
        if (f->get_family_id() == m.get_basic_family_id())
            return false;
        euf::th_model_builder* mb = func_decl2solver(f);
        return mb && mb->include_func_interp(f);
    }

    void solver::collect_dependencies(deps_t& deps) {
        for (enode* n : m_egraph.nodes()) {
            auto* mb = sort2solver(m.get_sort(n->get_expr()));
            if (mb)
                mb->add_dep(n, deps);
            else
                deps.insert(n, nullptr);
        }

        TRACE("euf",
              for (auto const& d : deps.deps()) 
                  if (d.m_value) {
                      tout << mk_bounded_pp(d.m_key->get_expr(), m) << ":\n";
                      for (auto* n : *d.m_value)
                          tout << "   " << mk_bounded_pp(n->get_expr(), m) << "\n";
                  }
              );
    }

    class solver::user_sort {
        ast_manager&      m;
        model_ref&        mdl;
        expr_ref_vector&  values;
        user_sort_factory factory;
        scoped_ptr_vector<expr_ref_vector> sort_values;
        obj_map<sort, expr_ref_vector*>    sort2values;
    public:
        user_sort(solver& s, expr_ref_vector& values, model_ref& mdl): 
            m(s.m), mdl(mdl), values(values), factory(m) {}

        ~user_sort() {
            for (auto kv : sort2values) 
                mdl->register_usort(kv.m_key, kv.m_value->size(), kv.m_value->c_ptr());
        }

        void add(unsigned id, sort* srt) {
            expr_ref value(factory.get_fresh_value(srt), m);
            values.set(id, value);     
            expr_ref_vector* vals = nullptr;
            if (!sort2values.find(srt, vals)) {
                vals = alloc(expr_ref_vector, m);
                sort2values.insert(srt, vals);
                sort_values.push_back(vals);
            }
            vals->push_back(value);            
        }        
    };

    void solver::dependencies2values(deps_t& deps, model_ref& mdl) {
        user_sort user_sort(*this, m_values, mdl);
        for (enode* n : deps.top_sorted()) {
            unsigned id = n->get_root_id();
            if (m_values.get(id, nullptr))
                continue;
            expr* e = n->get_expr();
            m_values.reserve(id + 1);
            if (m.is_bool(e) && is_uninterp_const(e) && mdl->get_const_interp(to_app(e)->get_decl())) {
                m_values.set(id, mdl->get_const_interp(to_app(e)->get_decl()));
                continue;
            }
            // model of s() must have been fixed.
            if (m.is_bool(e)) {
                if (m.is_true(e)) {
                    m_values.set(id, m.mk_true());
                    continue;
                }
                if (m.is_false(e)) {
                    m_values.set(id, m.mk_false());
                    continue;
                }
                if (is_app(e) && to_app(e)->get_family_id() == m.get_basic_family_id())
                    continue;
                sat::bool_var v = get_enode(e)->bool_var();
                SASSERT(v != sat::null_bool_var);
                switch (s().value(v)) {
                case l_true:
                    m_values.set(id, m.mk_true());
                    break;
                case l_false:
                    m_values.set(id, m.mk_false());
                    break;
                default:
                    break;
                }
                continue;
            }
            sort* srt = m.get_sort(e);
            if (m.is_uninterp(srt)) 
                user_sort.add(id, srt);            
            else if (auto* mbS = sort2solver(srt))
                mbS->add_value(n, *mdl, m_values);
            else if (auto* mbE = expr2solver(e))
                mbE->add_value(n, *mdl, m_values);
            else {
                IF_VERBOSE(1, verbose_stream() << "no model values created for " << mk_pp(e, m) << "\n");
            }                
        }
    }

    void solver::values2model(deps_t const& deps, model_ref& mdl) {
        ptr_vector<expr> args;
        for (enode* n : deps.top_sorted()) {
            expr* e = n->get_expr();
            if (!is_app(e))
                continue;
            app* a = to_app(e);
            func_decl* f = a->get_decl();            
            if (!include_func_interp(f))
                continue;
            if (m.is_bool(e) && is_uninterp_const(e) && mdl->get_const_interp(f))
                continue;
            expr* v = m_values.get(n->get_root_id());
            CTRACE("euf", !v, tout << "no value for " << mk_pp(e, m) << "\n";);
            if (!v)
                continue;
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
                for (enode* arg : enode_args(n)) {
                    args.push_back(m_values.get(arg->get_root_id()));
                    SASSERT(args.back());
                }
                SASSERT(args.size() == arity);
                if (!fi->get_entry(args.c_ptr()))
                    fi->insert_new_entry(args.c_ptr(), v);
            }
        }
    }

    void solver::register_macros(model& mdl) {
        // TODO
    }

    obj_map<expr,enode*> const& solver::values2root() {    
        if (!m_values2root.empty())
            return m_values2root;
        for (enode* n : m_egraph.nodes())
            if (n->is_root() && m_values.get(n->get_expr_id()))
                m_values2root.insert(m_values.get(n->get_expr_id()), n);
        return m_values2root;
    }

    void solver::validate_model(model& mdl) {
        for (enode* n : m_egraph.nodes()) {
            expr* e = n->get_expr();
            if (!m.is_bool(e))
                continue;
            unsigned id = n->get_root_id();
            if (!m_values.get(id))
                continue;
            bool tt = m.is_true(m_values.get(id));
            if (mdl.is_true(e) != tt) {
                IF_VERBOSE(0, verbose_stream() << "Failed to evaluate " << id << " " << mk_bounded_pp(e, m) << " " << mdl(e) << " " << mk_bounded_pp(m_values.get(id), m) << "\n");
            }
        }
        
    }


}
