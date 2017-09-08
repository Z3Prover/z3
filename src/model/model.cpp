/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    model.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2011-04-30.

Revision History:

--*/
#include "model/model.h"
#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include "ast/rewriter/var_subst.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/array_decl_plugin.h"
#include "ast/well_sorted.h"
#include "ast/used_symbols.h"
#include "ast/for_each_expr.h"
#include "model/model_evaluator.h"

model::model(ast_manager & m):
    model_core(m),
    m_cleaned(false) {
}

model::~model() {
    for (auto & kv : m_usort2universe) {
        m_manager.dec_ref(kv.m_key);
        m_manager.dec_array_ref(kv.m_value->size(), kv.m_value->c_ptr());
        dealloc(kv.m_value);
    }
}



void model::copy_const_interps(model const & source) {
    for (auto const& kv : source.m_interp) 
        register_decl(kv.m_key, kv.m_value);
}

void model::copy_func_interps(model const & source) {
    for (auto const& kv : source.m_finterp) 
        register_decl(kv.m_key, kv.m_value->copy());
}

void model::copy_usort_interps(model const & source) {
    for (auto const& kv : source.m_usort2universe) 
        register_usort(kv.m_key, kv.m_value->size(), kv.m_value->c_ptr());
}

model * model::copy() const {
    model * m = alloc(model, m_manager);

    m->copy_const_interps(*this);
    m->copy_func_interps(*this);
    m->copy_usort_interps(*this);

    return m;
}

// Remark: eval is for backward compatibility. We should use model_evaluator.
bool model::eval(expr * e, expr_ref & result, bool model_completion) {
    model_evaluator ev(*this);
    ev.set_model_completion(model_completion);
    try {
        ev(e, result);
        return true;
    }
    catch (model_evaluator_exception & ex) {
        (void)ex;
        TRACE("model_evaluator", tout << ex.msg() << "\n";);
        return false;
    }
}

struct model::value_proc : public some_value_proc {
    model & m_model;
    value_proc(model & m):m_model(m) {}
    virtual expr * operator()(sort * s) {
        ptr_vector<expr> * u = 0;
        if (m_model.m_usort2universe.find(s, u)) {
            if (u->size() > 0)
                return u->get(0);
        }
        return 0;
    }
};

expr * model::get_some_value(sort * s) {
    value_proc p(*this);
    return m_manager.get_some_value(s, &p);
}

ptr_vector<expr> const & model::get_universe(sort * s) const {
    ptr_vector<expr> * u = 0;
    m_usort2universe.find(s, u);
    SASSERT(u != 0);
    return *u;
}

bool model::has_uninterpreted_sort(sort * s) const {
    ptr_vector<expr> * u = 0;
    m_usort2universe.find(s, u);
    return u != 0;
}

unsigned model::get_num_uninterpreted_sorts() const {
    return m_usorts.size();
}

sort * model::get_uninterpreted_sort(unsigned idx) const {
    return m_usorts[idx];
}

void model::register_usort(sort * s, unsigned usize, expr * const * universe) {
    sort2universe::obj_map_entry * entry = m_usort2universe.insert_if_not_there2(s, 0);
    m_manager.inc_array_ref(usize, universe);
    if (entry->get_data().m_value == 0) {
        // new entry
        m_usorts.push_back(s);
        m_manager.inc_ref(s);
        ptr_vector<expr> * new_u = alloc(ptr_vector<expr>);
        new_u->append(usize, universe);
        entry->get_data().m_value = new_u;
    }
    else {
        // updating
        ptr_vector<expr> * u = entry->get_data().m_value;
        SASSERT(u);
        m_manager.dec_array_ref(u->size(), u->c_ptr());
        u->append(usize, universe);
    }
}

model * model::translate(ast_translation & translator) const {
    model * res = alloc(model, translator.to());

    // Translate const interps
    for (auto const& kv : m_interp) 
        res->register_decl(translator(kv.m_key), translator(kv.m_value));

    // Translate func interps
    for (auto const& kv : m_finterp) {
        func_interp * fi = kv.m_value;
        res->register_decl(translator(kv.m_key), fi->translate(translator));
    }

    // Translate usort interps
    for (auto const& kv : m_usort2universe) {
        ptr_vector<expr> new_universe;
        for (unsigned i=0; i < kv.m_value->size(); i++)
            new_universe.push_back(translator(kv.m_value->get(i)));
        res->register_usort(translator(kv.m_key),
                            new_universe.size(),
                            new_universe.c_ptr());
    }

    return res;
}

struct model::top_sort {
    th_rewriter                  m_rewrite;
    obj_map<func_decl, unsigned> m_partition_id;
    obj_map<func_decl, unsigned> m_dfs_num;
    ptr_vector<func_decl>        m_top_sorted;
    ptr_vector<func_decl>        m_stack_S;
    ptr_vector<func_decl>        m_stack_P;
    unsigned                     m_next_preorder;    
    obj_map<func_decl, func_decl_set*> m_deps;
    top_sort(ast_manager& m):
        m_rewrite(m)
    {}

    ~top_sort() {
        for (auto & kv : m_deps) dealloc(kv.m_value);
    }
};

void model::cleanup() {
    if (m_cleaned) return;

    // stratify m_finterp and m_decls in a topological sort
    // such that functions f1 < f2 then f1 does not use f2.
    // then for each function in order clean-up the interpretations
    // by substituting in auxiliary definitions that can be eliminated.

    top_sort st(m_manager);
    collect_deps(st.m_deps);
    topological_sort(st);
    for (func_decl * f : st.m_top_sorted) {
        cleanup_interp(st, f);
    }

    // remove auxiliary declarations that are not used.
    func_decl_set removed;
    for (func_decl * f : st.m_top_sorted) {
        if (f->is_skolem() && is_singleton_partition(st, f)) {
            unregister_decl(f);
            removed.insert(f);
        }
    }
    if (!removed.empty()) {
        remove_decls(m_decls, removed);
        remove_decls(m_func_decls, removed);
        remove_decls(m_const_decls, removed);
    }
    m_cleaned = true;
}


void model::collect_deps(obj_map<func_decl, func_decl_set*>& deps) {
    for (auto const& kv : m_finterp) {
        deps.insert(kv.m_key, collect_deps(kv.m_value));
    }
    for (auto const& kv : m_interp) {
        deps.insert(kv.m_key, collect_deps(kv.m_value));
    }
}

struct model::deps_collector {
    model& m;
    func_decl_set& s;
    array_util autil;
    deps_collector(model& m, func_decl_set& s): m(m), s(s), autil(m.get_manager()) {}
    void operator()(app* a) {
        func_decl* f = a->get_decl();
        if (autil.is_as_array(f)) {
            f = autil.get_as_array_func_decl(a);
        }
        if (m.has_interpretation(f)) {
            s.insert(f);
        }
    }
    void operator()(expr* ) {}
};


model::func_decl_set* model::collect_deps(expr * e) {
    func_decl_set* s = alloc(func_decl_set);
    deps_collector collector(*this, *s);
    if (e) for_each_expr(collector, e);
    return s;
}

model::func_decl_set* model::collect_deps(func_interp * fi) {
    func_decl_set* s = alloc(func_decl_set);
    deps_collector collector(*this, *s);
    expr* e = fi->get_else();
    if (e) for_each_expr(collector, e);
    return s;
}

void model::topological_sort(top_sort& st) {
    st.m_next_preorder = 0;
    st.m_partition_id.reset();
    st.m_top_sorted.reset();
    for (auto & kv : st.m_deps) {
        traverse(st, kv.m_key);
    }
    SASSERT(st.m_stack_S.empty());
    SASSERT(st.m_stack_P.empty());
    st.m_dfs_num.reset();
}

void model::traverse(top_sort& st, func_decl* f) {
    unsigned p_id = 0;
    if (st.m_dfs_num.find(f, p_id)) {
        if (!st.m_partition_id.contains(f)) {
            while (!st.m_stack_P.empty() && st.m_partition_id[st.m_stack_P.back()] > p_id) {
                st.m_stack_P.pop_back();
            }
        }
    }
    else {
        st.m_dfs_num.insert(f, st.m_next_preorder++);        
        st.m_stack_S.push_back(f);
        st.m_stack_P.push_back(f);        
        for (func_decl* g : *st.m_deps[f]) {
            traverse(st, g);
        }        
        if (f == st.m_stack_P.back()) {
            
            p_id = st.m_top_sorted.size();            
            func_decl* s_f;
            do {
                s_f = st.m_stack_S.back();
                st.m_stack_S.pop_back();
                st.m_top_sorted.push_back(s_f);
                st.m_partition_id.insert(s_f, p_id);
            } 
            while (s_f != f);
            st.m_stack_P.pop_back();
        }
    }
}

bool model::is_singleton_partition(top_sort& st, func_decl* f) const {
    unsigned pid = st.m_partition_id[f];
    return f == st.m_top_sorted[pid] &&
        (pid == 0 || st.m_partition_id[st.m_top_sorted[pid-1]] != pid) && 
        (pid + 1 == st.m_top_sorted.size() || st.m_partition_id[st.m_top_sorted[pid+1]] != pid);
}

/**
   \brief Inline interpretations of skolem functions
*/

void model::cleanup_interp(top_sort& st, func_decl* f) {
    unsigned pid = st.m_partition_id[f];
    expr * e1 = get_const_interp(f);
    if (e1) {
        expr_ref e2 = cleanup_expr(st, e1, pid);
        if (e2 != e1) 
            register_decl(f, e2);
        return;
    }
    func_interp* fi = get_func_interp(f);
    if (fi) {
        e1 = fi->get_else();
        expr_ref e2 = cleanup_expr(st, e1, pid);
        if (e1 != e2) 
            fi->set_else(e2);
#if 0
        // not required so far given that entries are values.
        for (func_entry * e : *fi) {
            // e->args_are_values();
            e1 = e->get_result();
            e2 = cleanup_expr(st, e1, pid);
            if (e1 != e2) 
                e->set_result(m_manager, e2); // expose private method?
        }
#endif
    }
}


expr_ref model::cleanup_expr(top_sort& st, expr* e, unsigned current_partition) {
    if (!e) return expr_ref(0, m_manager);

    TRACE("model", tout << "cleaning up:\n" << mk_pp(e, m_manager) << "\n";);

    obj_map<expr, expr*> cache;
    expr_ref_vector trail(m_manager);
    ptr_buffer<expr, 128> todo;
    ptr_buffer<expr> args;
    todo.push_back(e);
    array_util autil(m_manager);
    func_interp* fi;

    while (!todo.empty()) {
        expr* a = todo.back();
        switch(a->get_kind()) {
        case AST_APP: {
            app * t = to_app(a);
            func_decl* f = t->get_decl();
            bool visited = true;
            expr_ref new_t(m_manager);
            
            args.reset();
            for (expr* t_arg : *t) {
                expr * arg = 0;
                if (!cache.find(t_arg, arg)) {
                    visited = false;
                    todo.push_back(t_arg);
                }
                else {
                    args.push_back(arg);
                }
            }
            if (!visited) {
                continue;
            }
            fi = 0;
            if (autil.is_as_array(a)) {
                func_decl* f = autil.get_as_array_func_decl(a);
                fi = get_func_interp(f);
            }
            
            if (fi && fi->get_interp()) {
                f = autil.get_as_array_func_decl(a);
                expr_ref_vector sargs(m_manager);
                sort_ref_vector vars(m_manager);
                svector<symbol> var_names;
                for (unsigned i = 0; i < f->get_arity(); ++i) {
                    var_names.push_back(symbol(i));
                    vars.push_back(f->get_domain(f->get_arity() - i - 1));
                }
                new_t = m_manager.mk_lambda(vars.size(), vars.c_ptr(), var_names.c_ptr(), fi->get_interp());
            }
            else if (f->is_skolem() && (fi = get_func_interp(f)) && fi->get_interp() && st.m_partition_id[f] != current_partition) {
                var_subst vs(m_manager);
                // ? args.reverse();
                vs(fi->get_interp(), args.size(), args.c_ptr(), new_t);
            }
            else if (is_uninterp_const(a) && !get_const_interp(f)) {
                new_t = get_some_value(f->get_range());
                register_decl(f, new_t);                
            }
            else {
                new_t = st.m_rewrite.mk_app(f, args.size(), args.c_ptr());
            }
            
            if (t != new_t.get()) trail.push_back(new_t);
            todo.pop_back();
            cache.insert(t, new_t);
            break;
        }
        default:
            SASSERT(a != 0);
            cache.insert(a, a);
            todo.pop_back();
            break;
        }
    }

    return expr_ref(cache[e], m_manager);
}

void model::remove_decls(ptr_vector<func_decl> & decls, func_decl_set const & s) {
    unsigned sz = decls.size();
    unsigned i  = 0;
    unsigned j  = 0;
    for (; i < sz; i++) {
        func_decl * f = decls[i];
        if (!s.contains(f)) {
            decls[j] = f;
            j++;
        }
    }
    decls.shrink(j);
}

