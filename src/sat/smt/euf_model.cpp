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

    class solver::user_sort {
        ast_manager& m;
        model_ref& mdl;
        expr_ref_vector& values;
        user_sort_factory factory;
        scoped_ptr_vector<expr_ref_vector> sort_values;
        obj_map<sort, expr_ref_vector*>    sort2values;
    public:
        user_sort(solver& s, expr_ref_vector& values, model_ref& mdl) :
            m(s.m), mdl(mdl), values(values), factory(m) {}

        ~user_sort() {
            for (auto kv : sort2values)
                mdl->register_usort(kv.m_key, kv.m_value->size(), kv.m_value->data());
        }

        void add(enode* r, sort* srt) {
            unsigned id = r->get_expr_id();
            expr_ref value(m);
            if (m.is_value(r->get_expr())) 
                value = r->get_expr();
            else 
                value = factory.get_fresh_value(srt);
            values.set(id, value);
            expr_ref_vector* vals = nullptr;
            if (!sort2values.find(srt, vals)) {
                vals = alloc(expr_ref_vector, m);
                sort2values.insert(srt, vals);
                sort_values.push_back(vals);
            }
            vals->push_back(value);
        }

        void register_value(expr* val) {
            factory.register_value(val);
        }
    };

    void solver::update_model(model_ref& mdl) {
        for (auto* mb : m_solvers)
            mb->init_model();
        m_values.reset();
        m_values2root.reset();
        deps_t deps;
        user_sort us(*this, m_values, mdl);
        collect_dependencies(us, deps);
        deps.topological_sort();
        dependencies2values(us, deps, mdl);
        values2model(deps, mdl);
        for (auto* mb : m_solvers)
            mb->finalize_model(*mdl);
        TRACE("model", tout << "created model " << *mdl << "\n";);
        validate_model(*mdl);
    }

    bool solver::include_func_interp(func_decl* f) {
        if (f->get_family_id() == null_family_id)
            return true;
        if (f->get_family_id() == m.get_basic_family_id())
            return false;
        if (f->is_skolem())
            return false;
        euf::th_model_builder* mb = func_decl2solver(f);
        return mb && mb->include_func_interp(f);
    }

    void solver::collect_dependencies(user_sort& us, deps_t& deps) {
        ptr_buffer<enode> fresh_values;
        for (enode* n : m_egraph.nodes()) {
            expr* e = n->get_expr();
            sort* srt = e->get_sort();
            auto* mb = sort2solver(srt);
            if (!mb) 
                deps.insert(n, nullptr);
            else if (!mb->add_dep(n, deps))
                fresh_values.push_back(n);
            if (n->is_root() && m.is_uninterp(srt) && m.is_value(e))
                us.register_value(e);
        }

        // fresh values depend on all non-fresh values of the same sort
        for (enode* n : fresh_values) {
            n->mark1();
            deps.insert(n, nullptr);
        }
        for (enode* n : fresh_values)
            for (enode* r : m_egraph.nodes())
                if (r->is_root() && r->get_sort() == n->get_sort() && !r->is_marked1())
                    deps.add(n, r);
        for (enode* n : fresh_values)
            n->unmark1();
        
        TRACE("euf",
              for (auto const& d : deps.deps()) 
                  if (d.m_value) {
                      tout << bpp(d.m_key) << ":\n";
                      for (auto* n : *d.m_value)
                          tout << "   " << bpp(n) << "\n";
                  }
              );
    }

    void solver::dependencies2values(user_sort& us, deps_t& deps, model_ref& mdl) {
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
                switch (n->value()) {
                case l_true:
                    m_values.set(id, m.mk_true());
                    continue;
                case l_false:
                    m_values.set(id, m.mk_false());
                    continue;
                default:
                    break;
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
            sort* srt = e->get_sort();
            if (m.is_uninterp(srt)) 
                us.add(n->get_root(), srt);
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
                for (expr* arg : *a) {
                    enode* earg = get_enode(arg); 
                    args.push_back(m_values.get(earg->get_root_id()));                
                    CTRACE("euf", !args.back(), tout << "no value for " << bpp(earg) << "\n";);
                    SASSERT(args.back());
                }
                SASSERT(args.size() == arity);
                if (!fi->get_entry(args.data()))
                    fi->insert_new_entry(args.data(), v);
                TRACE("euf", tout << f->get_name() << "\n";
                      for (expr* arg : args) tout << mk_pp(arg, m) << " ";
                      tout << "\n -> " << mk_pp(v, m) << "\n";);

            }
        }
    }

    void solver::register_macros(model& mdl) {
        // TODO
    }

    void solver::model_updated(model_ref& mdl) {
        m_values2root.reset();
        for (enode* n : m_egraph.nodes())
            if (n->is_root() && m_values.get(n->get_expr_id())) 
                m_values[n->get_expr_id()] = (*mdl)(n->get_expr());            
    }

    obj_map<expr,enode*> const& solver::values2root() {    
        if (!m_values2root.empty())
            return m_values2root;
        for (enode* n : m_egraph.nodes())
            if (n->is_root() && m_values.get(n->get_expr_id()))
                m_values2root.insert(m_values.get(n->get_expr_id()), n);
        TRACE("model", 
              for (auto kv : m_values2root) 
                  tout << mk_pp(kv.m_key, m) << " -> " << bpp(kv.m_value) << "\n";);
        
        return m_values2root;
    }

    expr* solver::node2value(enode* n) const {
        return m_values.get(n->get_root_id(), nullptr);
    }

    void solver::validate_model(model& mdl) {
        bool first = true;
        for (enode* n : m_egraph.nodes()) {
            expr* e = n->get_expr();
            if (!m.is_bool(e))
                continue;
            if (has_quantifiers(e))
                continue;
            if (!is_relevant(n))
                continue;
            bool tt = l_true == s().value(n->bool_var());
            if (tt && !mdl.is_false(e))
                continue;
            if (!tt && !mdl.is_true(e))
                continue;
            IF_VERBOSE(0, 
                       verbose_stream() << "Failed to validate " << n->bool_var() << " " << bpp(n) << " " << mdl(e) << "\n";
                       for (auto* arg : euf::enode_args(n))
                           verbose_stream() << bpp(arg) << "\n" << mdl(arg->get_expr()) << "\n";);
            CTRACE("euf", first, 
                   tout << "Failed to validate " << n->bool_var() << " " << bpp(n) << " " << mdl(e) << "\n";
                   s().display(tout);
                   tout << mdl << "\n";);
            first = false;
        }
        
    }


}
