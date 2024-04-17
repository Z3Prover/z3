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
#include "sat/smt/sls_solver.h"
#include "model/value_factory.h"

namespace euf {

    class solver::user_sort {
        solver& s;
        ast_manager& m;
        model_ref& mdl;
        expr_ref_vector& values;
        user_sort_factory factory;
        scoped_ptr_vector<expr_ref_vector> sort_values;
        obj_map<sort, expr_ref_vector*>    sort2values;
    public:
        user_sort(solver& s, expr_ref_vector& values, model_ref& mdl) :
            s(s), m(s.m), mdl(mdl), values(values), factory(m) {}

        ~user_sort() {
            for (auto const& kv : sort2values)
                mdl->register_usort(kv.m_key, kv.m_value->size(), kv.m_value->data());
        }

        void add(enode* r, sort* srt) {
            unsigned id = r->get_expr_id();
            expr_ref value(m);
            if (m.is_value(r->get_expr()))
                value = r->get_expr();
            else
                value = factory.get_fresh_value(srt);
            (void)s;
            TRACE("model", tout << s.bpp(r) << " := " << value << "\n";);
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

    void solver::save_model(model_ref& mdl) {
        m_qmodel = mdl;
    }

    model_ref solver::get_sls_model() {
        model_ref mdl;
        auto s = get_solver(m.mk_family_id("sls"), nullptr);
        if (s)
            mdl = dynamic_cast<sls::solver*>(s)->get_model();
        return mdl;
    }

    void solver::update_model(model_ref& mdl, bool validate) {
        TRACE("model", tout << "create model\n";);
        if (m_qmodel) {
            mdl = m_qmodel;
            return;
        }
        mdl->reset_eval_cache();        
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
        if (validate)
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
        
        TRACE("model",
              for (auto * t : deps.deps()) {
                  auto* v = deps.get_dep(t);
                  if (v) {
                      tout << bpp(t) << ":\n";
                      for (auto* n : *v)
                          tout << "   " << bpp(n) << "\n";
                  }
              }
              );
    }

    void solver::dependencies2values(user_sort& us, deps_t& deps, model_ref& mdl) {
        for (enode* n : deps.top_sorted()) {
            TRACE("model", tout << bpp(n->get_root()) << "\n");
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
                sat::bool_var v = get_enode(e)->bool_var();
                if (v == sat::null_bool_var)
                    continue;
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
            else if (is_app(e) && to_app(e)->get_family_id() != m.get_basic_family_id()) {
                m_values.set(id, e);
                IF_VERBOSE(1, verbose_stream() << "creating self-value for " << mk_pp(e, m) << "\n");
            }
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
            if (!is_relevant(n))
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
                    expr* val = m_values.get(earg->get_root_id());
                    args.push_back(val);                
                    CTRACE("euf", !val, tout << "no value for " << bpp(earg) << "\n" << bpp(n) << "\n"; display(tout););
                    SASSERT(val);
                }
                SASSERT(args.size() == arity);
                if (!fi->get_entry(args.data()))
                    fi->insert_new_entry(args.data(), v);
                TRACE("euf", tout << bpp(n) << " " << f->get_name() << "\n";
                      for (expr* arg : args) tout << mk_pp(arg, m) << " ";
                      tout << "\n -> " << mk_pp(v, m) << "\n";
		      for (euf::enode* arg : euf::enode_args(n)) tout << bpp(arg) << " ";
		      tout << "\n";
		      );

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
              for (auto const& kv : m_values2root) 
                  tout << mk_bounded_pp(kv.m_key, m) << "\n    -> " << bpp(kv.m_value) << "\n";);
        
        return m_values2root;
    }

    expr* solver::node2value(enode* n) const {
        return m_values.get(n->get_root_id(), nullptr);
    }

    void solver::display_validation_failure(std::ostream& out, model& mdl, enode* n) {
        out << "Failed to validate b" << n->bool_var() << " " << bpp(n) << " " << mdl(n->get_expr()) << "\n";
        s().display(out);
        euf::enode_vector nodes;
        nodes.push_back(n);
        for (unsigned i = 0; i < nodes.size(); ++i) {
            euf::enode* r = nodes[i];
            if (!r || r->is_marked1())
                continue;
            r->mark1();
            if (is_app(r->get_expr()))
                for (auto* arg : *r->get_app())
                    nodes.push_back(get_enode(arg));
            expr_ref val = mdl(r->get_expr());
            expr_ref sval(m);
            th_rewriter rw(m);
            rw(val, sval);
            expr_ref mval = mdl(r->get_root()->get_expr());
            if (mval != sval) {
                if (r->bool_var() != sat::null_bool_var)
                    out << "b" << r->bool_var() << " ";
                out << bpp(r) << " :=\nvalue obtained from model:  " << sval << "\nvalue of the root expression:  " << mval << "\n";
                continue;
            }
            if (!m.is_bool(val))
                continue;
            auto bval = s().value(r->bool_var());
            bool tt = l_true == bval;
            if (tt != m.is_true(sval))
                out << bpp(r) << " :=\nvalue according to model:  " << sval << "\nvalue of Boolean literal:  " << bval << "\n";
        }
        for (euf::enode* r : nodes)
            if (r)
                r->unmark1();
        out << mdl << "\n";
    }

    void solver::validate_model(model& mdl) {       
        if (!m_unhandled_functions.empty())
            return;
        if (get_config().m_arith_ignore_int)
            return;
        for (auto* s : m_solvers)
            if (s && s->has_unhandled())
                return;
        model_evaluator ev(mdl);
        ev.set_model_completion(true);
        TRACE("model",
            for (enode* n : m_egraph.nodes()) {
                if (!is_relevant(n))
                    continue;
                unsigned id = n->get_root_id();
                expr* val = m_values.get(id, nullptr);
                if (!val)
                    continue;
                expr_ref mval = ev(n->get_expr());
                if (m.is_value(mval) && val != mval)
                    tout << "#" << bpp(n) << " := " << mk_pp(val, m) << " ~ " << mval << "\n";
            });
        bool first = true;
        for (enode* n : m_egraph.nodes()) {
            expr* e = n->get_expr();
            if (!m.is_bool(e))
                continue;
            if (has_quantifiers(e))
                continue;
            if (!is_relevant(n))
                continue;
            if (n->bool_var() == sat::null_bool_var)
                continue;
            bool tt = l_true == s().value(n->bool_var());
            if (tt && !mdl.is_false(e))
                continue;
            if (!tt && !mdl.is_true(e))
                continue;
            CTRACE("euf", first, display_validation_failure(tout, mdl, n););
            CTRACE("euf", first, display(tout));
            IF_VERBOSE(0, display_validation_failure(verbose_stream(), mdl, n););
            (void)first;
            first = false;
            exit(1);
        }        
    }


}
