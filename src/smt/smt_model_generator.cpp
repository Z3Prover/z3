/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_model_generator.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-10-29.

Revision History:

--*/

#include"smt_context.h"
#include"smt_model_generator.h"
#include"proto_model.h"
#include"for_each_expr.h"
#include"ast_ll_pp.h"
#include"ast_pp.h"
#include"ast_smt2_pp.h"

namespace smt {

    model_generator::model_generator(ast_manager & m):
        m_manager(m),
        m_context(0),
        m_fresh_idx(1),
        m_asts(m_manager),
        m_model(0) {
    }

    model_generator::~model_generator() {
    }

    void model_generator::reset() {
        m_extra_fresh_values.reset();
        m_fresh_idx = 1;
        m_root2value.reset();
        m_asts.reset();
        m_model = 0;
    }

    void model_generator::init_model() {
        SASSERT(!m_model);
        // PARAM-TODO smt_params ---> params_ref
        m_model = alloc(proto_model, m_manager, m_context->get_simplifier()); // , m_context->get_fparams());
        ptr_vector<theory>::const_iterator it  = m_context->begin_theories();
        ptr_vector<theory>::const_iterator end = m_context->end_theories();
        for (; it != end; ++it) {
            TRACE("model_generator_bug", tout << "init_model for theory: " << (*it)->get_name() << "\n";);
            (*it)->init_model(*this);
        }
    }

    /**
       \brief Create the boolean assignment.
    */
    void model_generator::mk_bool_model() {
        unsigned sz = m_context->get_num_b_internalized();
        for (unsigned i = 0; i < sz; i++) {
            expr * p = m_context->get_b_internalized(i);
            if (is_uninterp_const(p) && m_context->is_relevant(p)) {
                SASSERT(m_manager.is_bool(p));
                func_decl * d = to_app(p)->get_decl();
                lbool val     = m_context->get_assignment(p);
                expr * v      = val == l_true ? m_manager.mk_true() : m_manager.mk_false();
                m_model->register_decl(d, v);
            }
        }
    }

    /**
       \brief Create the mapping root2proc: enode-root -> model_value_proc, and roots.
       Store the new model_value_proc at procs.
    */
    void model_generator::mk_value_procs(obj_map<enode, model_value_proc *> & root2proc, ptr_vector<enode> & roots, 
                                         ptr_vector<model_value_proc> & procs) {
        ptr_vector<enode>::const_iterator it  = m_context->begin_enodes();
        ptr_vector<enode>::const_iterator end = m_context->end_enodes();
        for (; it != end; ++it) {
            enode * r = *it;
            if (r == r->get_root() && m_context->is_relevant(r)) {
                roots.push_back(r);
                sort * s      = m_manager.get_sort(r->get_owner());
                model_value_proc * proc = 0;
                if (m_manager.is_bool(s)) {
                    SASSERT(m_context->get_assignment(r) == l_true || m_context->get_assignment(r) == l_false);
                    if (m_context->get_assignment(r) == l_true)
                        proc = alloc(expr_wrapper_proc, m_manager.mk_true());
                    else
                        proc = alloc(expr_wrapper_proc, m_manager.mk_false());
                }
                else {
                    family_id fid = s->get_family_id();
                    theory * th   = m_context->get_theory(fid);
                    if (th && th->build_models()) {
                        if (r->get_th_var(th->get_id()) != null_theory_var) {
                            proc = th->mk_value(r, *this);
                            SASSERT(proc);
                        }
                        else {
                            TRACE("model_bug", tout << "creating fresh value for #" << r->get_owner_id() << "\n";);
                            proc = alloc(fresh_value_proc, mk_extra_fresh_value(m_manager.get_sort(r->get_owner())));
                        }
                    }
                    else {
                        proc = mk_model_value(r);
                        SASSERT(proc);
                    }
                }
                SASSERT(proc);
                procs.push_back(proc);
                root2proc.insert(r, proc);
            }
        }
    }
    
    model_value_proc* model_generator::mk_model_value(enode* r) {
        SASSERT(r == r->get_root());
        expr * n = r->get_owner();
        if (!m_manager.is_model_value(n)) {
            sort * s = m_manager.get_sort(r->get_owner());
            n = m_model->get_fresh_value(s);
            CTRACE("model_generator_bug", n == 0, 
                   tout << mk_pp(r->get_owner(), m_manager) << "\nsort:\n" << mk_pp(s, m_manager) << "\n";
                   tout << "is_finite: " << m_model->is_finite(s) << "\n";);
        }
        return alloc(expr_wrapper_proc, to_app(n));
    }

#define White 0
#define Grey  1
#define Black 2
    
    static int get_color(source2color const & colors, source const & s) {
        int color;
        if (colors.find(s, color))
            return color;
        return White;
    }
    
    static void set_color(source2color & colors, source const & s, int c) {
        colors.insert(s, c);
    }
    
    static void visit_child(source const & s, source2color & colors, svector<source> & todo, bool & visited) {
        if (get_color(colors, s) == White) {
            todo.push_back(s);
            visited = false;
        }
    }
    
    bool model_generator::visit_children(source const & src, 
                                         ptr_vector<enode> const & roots, 
                                         obj_map<enode, model_value_proc *> const & root2proc, 
                                         source2color & colors, 
                                         obj_hashtable<sort> & already_traversed, 
                                         svector<source> & todo) {
        if (src.is_fresh_value()) {
            // there is an implicit dependency between a fresh value stub of sort S and the root enodes of sort S that are not associated with fresh values.
            sort * s     = src.get_value()->get_sort();
            if (already_traversed.contains(s))
                return true;
            bool visited = true;
            unsigned sz  = roots.size();
            for (unsigned i = 0; i < sz; i++) {
                enode * r     = roots[i];
                if (m_manager.get_sort(r->get_owner()) != s)
                    continue;
                SASSERT(r == r->get_root());
                model_value_proc * proc = 0;
                root2proc.find(r, proc);
                SASSERT(proc);
                if (proc->is_fresh())
                    continue; // r is associated with a fresh value...
                SASSERT(r == r->get_root());
                TRACE("mg_top_sort", tout << "fresh!" << src.get_value()->get_idx() << " -> #" << r->get_owner_id() << " " << mk_pp(m_manager.get_sort(r->get_owner()), m_manager) << "\n";);
                visit_child(source(r), colors, todo, visited);
                TRACE("mg_top_sort", tout << "visited: " << visited << ", todo.size(): " << todo.size() << "\n";);
            }
            already_traversed.insert(s);
            return visited;
        }
        
        SASSERT(!src.is_fresh_value());

        enode * n = src.get_enode();
        SASSERT(n == n->get_root());
        bool visited = true;
        model_value_proc * proc = 0;
        root2proc.find(n, proc);
        SASSERT(proc);
        buffer<model_value_dependency> dependencies;
        proc->get_dependencies(dependencies);
        buffer<model_value_dependency>::const_iterator it  = dependencies.begin();
        buffer<model_value_dependency>::const_iterator end = dependencies.end();
        for (; it != end; ++it) {
            model_value_dependency const & dep = *it;
            visit_child(dep, colors, todo, visited);
            TRACE("mg_top_sort", tout << "#" << n->get_owner_id() << " -> ";
                  if (dep.is_fresh_value()) tout << "fresh!" << dep.get_value()->get_idx();
                  else tout << "#" << dep.get_enode()->get_owner_id();
                  tout << "\n";);
        }
        return visited;
    }

    void model_generator::process_source(source const & src,
                                         ptr_vector<enode> const & roots, 
                                         obj_map<enode, model_value_proc *> const & root2proc, 
                                         source2color & colors, 
                                         obj_hashtable<sort> & already_traversed, 
                                         svector<source> & todo,
                                         svector<source> & sorted_sources) {
        TRACE("mg_top_sort", tout << "process source, is_fresh: " << src.is_fresh_value() << " ";
              if (src.is_fresh_value()) tout << "fresh!" << src.get_value()->get_idx();
              else tout << "#" << src.get_enode()->get_owner_id();
              tout << ", todo.size(): " << todo.size() << "\n";);
        int color     = get_color(colors, src);
        SASSERT(color != Grey);
        if (color == Black)
            return;
        SASSERT(color == White);
        todo.push_back(src);
        while (!todo.empty()) {
            source curr = todo.back();
            TRACE("mg_top_sort", tout << "current source, is_fresh: " << curr.is_fresh_value() << " ";
                  if (curr.is_fresh_value()) tout << "fresh!" << curr.get_value()->get_idx();
                  else tout << "#" << curr.get_enode()->get_owner_id();
                  tout << ", todo.size(): " << todo.size() << "\n";);
            switch (get_color(colors, curr)) {
            case White:
                set_color(colors, curr, Grey);
                visit_children(curr, roots, root2proc, colors, already_traversed, todo);
                break;
            case Grey:
                SASSERT(visit_children(curr, roots, root2proc, colors, already_traversed, todo));
                set_color(colors, curr, Black);
                sorted_sources.push_back(curr);
                break;
            case Black:
                todo.pop_back();
                break;
            default:
                UNREACHABLE();
            }
        }
        TRACE("mg_top_sort", tout << "END process_source, todo.size(): " << todo.size() << "\n";);
    }

    /**
       \brief Topological sort of 'sources'. Store result in sorted_sources.
    */
    void model_generator::top_sort_sources(ptr_vector<enode> const & roots, 
                                           obj_map<enode, model_value_proc *> const & root2proc, 
                                           svector<source> & sorted_sources) {
        
        svector<source>     todo;
        source2color        colors;
        // The following 'set' of sorts is used to avoid traversing roots looking for enodes of sort S.
        // That is, a sort S is in already_traversed, if all enodes of sort S in roots were already traversed.
        obj_hashtable<sort> already_traversed;

        // topological sort

        // traverse all extra fresh values...
        unsigned sz = m_extra_fresh_values.size();
        for (unsigned i = 0; i < sz; i++) {
            extra_fresh_value * f = m_extra_fresh_values[i];
            process_source(source(f), roots, root2proc, colors, already_traversed, todo, sorted_sources);
        }

        // traverse all enodes that are associated with fresh values...
        sz = roots.size();
        for (unsigned i = 0; i < sz; i++) {
            enode * r     = roots[i];
            model_value_proc * proc = 0;
            root2proc.find(r, proc);
            SASSERT(proc);
            if (!proc->is_fresh())
                continue;
            process_source(source(r), roots, root2proc, colors, already_traversed, todo, sorted_sources);
        }

        sz = roots.size();
        for (unsigned i = 0; i < sz; i++) {
            enode * r     = roots[i];
            process_source(source(r), roots, root2proc, colors, already_traversed, todo, sorted_sources);
        }
    }

    void model_generator::mk_values() {
        obj_map<enode, model_value_proc *> root2proc;
        ptr_vector<enode> roots;
        ptr_vector<model_value_proc> procs;
        svector<source> sources;
        buffer<model_value_dependency> dependencies;
        ptr_vector<expr> dependency_values;
        mk_value_procs(root2proc, roots, procs);
        top_sort_sources(roots, root2proc, sources);
        TRACE("sorted_sources",
              svector<source>::const_iterator it  = sources.begin();
              svector<source>::const_iterator end = sources.end();
              for (; it != end; ++it) {
                  source const & curr = *it;
                  if (curr.is_fresh_value()) {
                      tout << "fresh!" << curr.get_value()->get_idx() << " " << mk_pp(curr.get_value()->get_sort(), m_manager) << "\n";
                  }
                  else {
                      enode * n = curr.get_enode();
                      SASSERT(n->get_root() == n);
                      sort * s = m_manager.get_sort(n->get_owner());
                      tout << "#" << n->get_owner_id() << " " << mk_pp(s, m_manager);
                      model_value_proc * proc = 0;
                      root2proc.find(n, proc);
                      SASSERT(proc);
                      tout << " is_fresh: " << proc->is_fresh() << "\n";
                  }
              });
        svector<source>::const_iterator it  = sources.begin();
        svector<source>::const_iterator end = sources.end();
        for (; it != end; ++it) {
            source const & curr = *it;
            
            if (curr.is_fresh_value()) {
                sort * s = curr.get_value()->get_sort();
                TRACE("model_fresh_bug", tout << "mk fresh!" << curr.get_value()->get_idx() << " : " << mk_pp(s, m_manager) << "\n";);
                expr * val = m_model->get_fresh_value(s);
                TRACE("model_fresh_bug", tout << "mk fresh!" << curr.get_value()->get_idx() << " := #" << (val == 0 ? UINT_MAX : val->get_id()) << "\n";);
                m_asts.push_back(val);
                curr.get_value()->set_value(val);
            }
            else {
                enode * n = curr.get_enode();
                SASSERT(n->get_root() == n);
                TRACE("mg_top_sort", tout << "#" << n->get_owner_id() << "\n";);
                dependencies.reset();
                dependency_values.reset();
                model_value_proc * proc = 0;
                VERIFY(root2proc.find(n, proc));
                SASSERT(proc);
                proc->get_dependencies(dependencies);
                buffer<model_value_dependency>::const_iterator it2  = dependencies.begin();
                buffer<model_value_dependency>::const_iterator end2 = dependencies.end();
                for (; it2 != end2; ++it2) {
                    model_value_dependency const & d = *it2;
                    if (d.is_fresh_value()) {
                        CTRACE("mg_top_sort", !d.get_value()->get_value(), 
                               tout << "#" << n->get_owner_id() << " -> ";
                               tout << "fresh!" << d.get_value()->get_idx() << "\n";);
                        SASSERT(d.get_value()->get_value());
                        dependency_values.push_back(d.get_value()->get_value());
                    }
                    else {
                        enode * child = d.get_enode();
                        child = child->get_root();
                        app * val = 0;
                        m_root2value.find(child, val);
                        SASSERT(val);
                        dependency_values.push_back(val);
                    }
                }
                app * val = proc->mk_value(*this, dependency_values); 
                register_value(val);
                m_asts.push_back(val);
                m_root2value.insert(n, val);
            }
        }
        std::for_each(procs.begin(), procs.end(), delete_proc<model_value_proc>());
        std::for_each(m_extra_fresh_values.begin(), m_extra_fresh_values.end(), delete_proc<extra_fresh_value>());
        m_extra_fresh_values.reset();
        
        // send model
        ptr_vector<enode>::const_iterator it3  = m_context->begin_enodes();
        ptr_vector<enode>::const_iterator end3 = m_context->end_enodes();
        for (; it3 != end3; ++it3) {
            enode * n = *it3;
            if (is_uninterp_const(n->get_owner()) && m_context->is_relevant(n)) {
                func_decl * d = n->get_owner()->get_decl();
                expr * val    = get_value(n);
                m_model->register_decl(d, val);
            }
        }
    }

    app * model_generator::get_value(enode * n) const {
        app * val = 0;
        m_root2value.find(n->get_root(), val);
        SASSERT(val);
        return val;
    }

    /**
       \brief Return true if the interpretation of the function should be included in the model.
    */
    bool model_generator::include_func_interp(func_decl * f) const {
        return f->get_family_id() == null_family_id;
    }
    
    /**
       \brief Create (partial) interpretation of function symbols.
       The "else" is missing.
    */
    void model_generator::mk_func_interps() {
        unsigned sz = m_context->get_num_e_internalized();
        for (unsigned i = 0; i < sz; i++) {
            expr * t  = m_context->get_e_internalized(i);
            if (!m_context->is_relevant(t))
                continue;
            enode * n         = m_context->get_enode(t);
            unsigned num_args = n->get_num_args();
            func_decl * f     = n->get_decl();
            if (num_args > 0 && n->get_cg() == n && include_func_interp(f)) {
                ptr_buffer<expr> args;
                expr * result = get_value(n);
                SASSERT(result);
                for (unsigned j = 0; j < num_args; j++) {
                    app * arg = get_value(n->get_arg(j));
                    SASSERT(arg);
                    args.push_back(arg);
                }
                func_interp * fi = m_model->get_func_interp(f);
                if (fi == 0) {
                    fi = alloc(func_interp, m_manager, f->get_arity());
                    m_model->register_decl(f, fi);
                }
                SASSERT(m_model->has_interpretation(f));
                SASSERT(m_model->get_func_interp(f) == fi);
                // The entry must be new because n->get_cg() == n
                TRACE("func_interp_bug", 
                      tout << "insert new entry for:\n" << mk_ismt2_pp(n->get_owner(), m_manager) << "\nargs: ";
                      for (unsigned i = 0; i < num_args; i++) {
                          tout << "#" << n->get_arg(i)->get_owner_id() << " ";
                      }
                      tout << "\n";
                      tout << "value: #" << n->get_owner_id() << "\n" << mk_ismt2_pp(result, m_manager) << "\n";);
                if (m_context->get_last_search_failure() == smt::THEORY) {
                    // if the theory solvers are incomplete, then we cannot assume the e-graph is close under congruence
                    if (fi->get_entry(args.c_ptr()) == 0)
                        fi->insert_new_entry(args.c_ptr(), result);
                }
                else {
                    fi->insert_new_entry(args.c_ptr(), result);
                }
            }
        }
    }

    extra_fresh_value * model_generator::mk_extra_fresh_value(sort * s) {
        SASSERT(s->is_infinite());
        extra_fresh_value * r = alloc(extra_fresh_value, s, m_fresh_idx);
        m_fresh_idx++;
        m_extra_fresh_values.push_back(r);
        return r;
    }

    expr * model_generator::get_some_value(sort * s) {
        SASSERT(m_model);
        return m_model->get_some_value(s);
    }

    void model_generator::register_value(expr * val) {
        SASSERT(m_model); 
        m_model->register_value(val); 
    }

    void model_generator::finalize_theory_models() {
        ptr_vector<theory>::const_iterator it  = m_context->begin_theories();
        ptr_vector<theory>::const_iterator end = m_context->end_theories();
        for (; it != end; ++it)
            (*it)->finalize_model(*this);
    } 

    void model_generator::register_existing_model_values() {
        ptr_vector<enode>::const_iterator it  = m_context->begin_enodes();
        ptr_vector<enode>::const_iterator end = m_context->end_enodes();
        for (; it != end; ++it) {
            enode * r = *it;
            if (r == r->get_root() && m_context->is_relevant(r)) {
                expr * n = r->get_owner();
                if (m_manager.is_model_value(n)) {
                    register_value(n);
                }
            }
        }
    }
    
    void model_generator::register_factory(value_factory * f) {
        m_model->register_factory(f); 
    }

    void model_generator::register_macros() {
        unsigned num = m_context->get_num_macros();
        TRACE("register_macros", tout << "num. macros: " << num << "\n";);
        expr_ref v(m_manager);
        for (unsigned i = 0; i < num; i++) {
            func_decl * f    = m_context->get_macro_interpretation(i, v);
            func_interp * fi = alloc(func_interp, m_manager, f->get_arity());
            fi->set_else(v);
            TRACE("register_macros", tout << f->get_name() << "\n" << mk_pp(v, m_manager) << "\n";);
            m_model->register_decl(f, fi);
        }
    }

    /**
       \brief Auxiliary functor for method register_indirect_elim_decls.
    */
    class mk_interp_proc {
        context &       m_context;
        proto_model &   m_model;
    public:
        mk_interp_proc(context & ctx, proto_model & m):
            m_context(ctx), 
            m_model(m) {
        }

        void operator()(var * n) { 
        }

        void operator()(app * n) { 
            if (!is_uninterp(n))
                return; // n is interpreted
            func_decl * d  = n->get_decl();
            if (m_model.has_interpretation(d))
                return; // declaration already has an interpretation.
            if (n->get_num_args() == 0) {
                sort * r = d->get_range();
                expr * v = m_model.get_some_value(r);
                m_model.register_decl(d, v);
            }
            else {
                func_interp * fi = alloc(func_interp, m_context.get_manager(), d->get_arity());            
                m_model.register_decl(d, fi);
            }
        }
        
        void operator()(quantifier * n) { 
        }
        
    };

    proto_model * model_generator::mk_model() {
        SASSERT(!m_model);
        TRACE("func_interp_bug", m_context->display(tout););
        init_model();
        register_existing_model_values();
        mk_bool_model();
        mk_values();
        mk_func_interps();
        finalize_theory_models();
        register_macros();
        return m_model;
    }
    
};
