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
#include "util/top_sort.h"
#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include "ast/rewriter/var_subst.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/array_decl_plugin.h"
#include "ast/well_sorted.h"
#include "ast/used_symbols.h"
#include "ast/for_each_expr.h"
#include "ast/for_each_ast.h"
#include "model/model.h"
#include "model/model_evaluator.h"

model::model(ast_manager & m):
    model_core(m),
    m_mev(*this),
    m_cleaned(false) {
}

model::~model() {
    for (auto & kv : m_usort2universe) {
        m.dec_ref(kv.m_key);
        m.dec_array_ref(kv.m_value->size(), kv.m_value->c_ptr());
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
    model * mdl = alloc(model, m);
    mdl->copy_const_interps(*this);
    mdl->copy_func_interps(*this);
    mdl->copy_usort_interps(*this);
    return mdl;
}

bool model::eval_expr(expr * e, expr_ref & result, bool model_completion) {
    scoped_model_completion _smc(*this, model_completion);
    try {
        result = (*this)(e);
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
    expr * operator()(sort * s) override {
        ptr_vector<expr> * u = nullptr;
        if (m_model.m_usort2universe.find(s, u)) {
            if (u->size() > 0)
                return u->get(0);
        }
        return nullptr;
    }
};

expr * model::get_some_value(sort * s) {
    value_proc p(*this);
    return m.get_some_value(s, &p);
}

ptr_vector<expr> const & model::get_universe(sort * s) const {
    ptr_vector<expr> * u = nullptr;
    m_usort2universe.find(s, u);
    SASSERT(u != nullptr);
    return *u;
}

bool model::has_uninterpreted_sort(sort * s) const {
    ptr_vector<expr> * u = nullptr;
    m_usort2universe.find(s, u);
    return u != nullptr;
}

unsigned model::get_num_uninterpreted_sorts() const {
    return m_usorts.size();
}

sort * model::get_uninterpreted_sort(unsigned idx) const {
    return m_usorts[idx];
}

void model::register_usort(sort * s, unsigned usize, expr * const * universe) {
    sort2universe::obj_map_entry * entry = m_usort2universe.insert_if_not_there2(s, 0);
    m.inc_array_ref(usize, universe);
    if (entry->get_data().m_value == 0) {
        // new entry
        m_usorts.push_back(s);
        m.inc_ref(s);
        ptr_vector<expr> * new_u = alloc(ptr_vector<expr>);
        new_u->append(usize, universe);
        entry->get_data().m_value = new_u;
    }
    else {
        // updating
        ptr_vector<expr> * u = entry->get_data().m_value;
        SASSERT(u);
        m.dec_array_ref(u->size(), u->c_ptr());
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
        for (expr* e : *kv.m_value) 
            new_universe.push_back(translator(e));
        res->register_usort(translator(kv.m_key),
                            new_universe.size(),
                            new_universe.c_ptr());
    }

    return res;
}

struct model::top_sort : public ::top_sort<func_decl> {
    th_rewriter                  m_rewrite;
    obj_map<func_decl, unsigned> m_occur_count;

    top_sort(ast_manager& m):
        m_rewrite(m)
    {}

    void add_occurs(func_decl* f) {
        m_occur_count.insert(f, occur_count(f) + 1);
    }

    unsigned occur_count(func_decl* f) const {
        unsigned count = 0;
        m_occur_count.find(f, count);
        return count;
    }

    ~top_sort() override {}
};

void model::compress() {
    if (m_cleaned) return;

    // stratify m_finterp and m_decls in a topological sort
    // such that functions f1 < f2 then f1 does not use f2.
    // then for each function in order clean-up the interpretations
    // by substituting in auxiliary definitions that can be eliminated.

    func_decl_ref_vector pinned(m);
    while (true) {
        top_sort ts(m);
        collect_deps(ts);
        ts.topological_sort();
        for (func_decl * f : ts.top_sorted()) {
            cleanup_interp(ts, f);
        }

        func_decl_set removed;
        ts.m_occur_count.reset();
        for (func_decl * f : ts.top_sorted()) {
            collect_occs(ts, f);
        }
        
        // remove auxiliary declarations that are not used.
        for (func_decl * f : ts.top_sorted()) {
            if (f->is_skolem() && ts.occur_count(f) == 0) {
                pinned.push_back(f);
                unregister_decl(f);
                removed.insert(f);
            }
        }
        if (removed.empty()) break;
        remove_decls(m_decls, removed);
        remove_decls(m_func_decls, removed);
        remove_decls(m_const_decls, removed);
    }
    m_cleaned = true;
    reset_eval_cache();
}


void model::collect_deps(top_sort& ts) {
    for (auto const& kv : m_finterp) {
        ts.insert(kv.m_key, collect_deps(ts, kv.m_value));
    }
    for (auto const& kv : m_interp) {
        ts.insert(kv.m_key, collect_deps(ts, kv.m_value));
    }
}

struct model::deps_collector {
    model&         m;
    top_sort&      ts;
    func_decl_set& s;
    array_util     autil;
    deps_collector(model& m, top_sort& ts, func_decl_set& s): m(m), ts(ts), s(s), autil(m.get_manager()) {}
    void operator()(app* a) {
        func_decl* f = a->get_decl();
        if (autil.is_as_array(f)) {
            f = autil.get_as_array_func_decl(a);            
        }
        if (m.has_interpretation(f)) {
            s.insert(f);
            ts.add_occurs(f);
        }
    }
    void operator()(expr* ) {}
};

struct model::occs_collector {
    top_sort&      ts;
    occs_collector(top_sort& ts): ts(ts) {}
    void operator()(func_decl* f) {
        ts.add_occurs(f);
    }
    void operator()(ast*) {}
};


model::func_decl_set* model::collect_deps(top_sort& ts, expr * e) {
    func_decl_set* s = alloc(func_decl_set);
    deps_collector collector(*this, ts, *s);
    if (e) for_each_expr(collector, e);
    return s;
}

model::func_decl_set* model::collect_deps(top_sort& ts, func_interp * fi) {
    func_decl_set* s = alloc(func_decl_set);
    deps_collector collector(*this, ts, *s);
    fi->compress();
    expr* e = fi->get_else();
    if (e) for_each_expr(collector, e);
    return s;
}


/**
   \brief Inline interpretations of skolem functions
*/

void model::cleanup_interp(top_sort& ts, func_decl* f) {
    unsigned pid = ts.partition_id(f);
    expr * e1 = get_const_interp(f);
    if (e1) {
        expr_ref e2 = cleanup_expr(ts, e1, pid);
        if (e2 != e1) 
            register_decl(f, e2);
        return;
    }
    func_interp* fi = get_func_interp(f);
    if (fi) {
        e1 = fi->get_else();
        expr_ref e2 = cleanup_expr(ts, e1, pid);
        if (e1 != e2) 
            fi->set_else(e2);
    }
}

void model::collect_occs(top_sort& ts, func_decl* f) {
    expr * e = get_const_interp(f);
    if (e) {
        collect_occs(ts, e);
    }
    else {
        func_interp* fi = get_func_interp(f);
        if (fi) {
            e = fi->get_else();
            collect_occs(ts, e);
        }
    }
}

void model::collect_occs(top_sort& ts, expr* e) {
    occs_collector collector(ts);
    for_each_ast(collector, e, true);
}

bool model::can_inline_def(top_sort& ts, func_decl* f) {
    if (ts.occur_count(f) <= 1) return true;
    func_interp* fi = get_func_interp(f);
    if (!fi) return false;
    if (fi->get_else() == nullptr) return false;
    expr* e = fi->get_else();
    obj_hashtable<expr> subs;
    ptr_buffer<expr> todo;
    todo.push_back(e);
    while (!todo.empty()) {
        if (fi->num_entries() + subs.size() > 8) return false;
        expr* e = todo.back();
        todo.pop_back();
        if (subs.contains(e)) continue;
        subs.insert(e);
        if (is_app(e)) {
            for (expr* arg : *to_app(e)) {
                todo.push_back(arg);
            }
        }
        else if (is_quantifier(e)) {
            todo.push_back(to_quantifier(e)->get_expr());
        }
    }
    return true;
}


expr_ref model::cleanup_expr(top_sort& ts, expr* e, unsigned current_partition) {
    if (!e) return expr_ref(nullptr, m);

    TRACE("model", tout << "cleaning up:\n" << mk_pp(e, m) << "\n";);

    obj_map<expr, expr*> cache;
    expr_ref_vector trail(m);
    ptr_buffer<expr, 128> todo;
    ptr_buffer<expr> args;
    todo.push_back(e);
    array_util autil(m);
    func_interp* fi = nullptr;
    unsigned pid = 0;
    expr_ref new_t(m);

    while (!todo.empty()) {
        expr* a = todo.back();
        switch(a->get_kind()) {
        case AST_APP: {
            app * t = to_app(a);
            func_decl* f = t->get_decl();
            bool visited = true;
            
            args.reset();
            for (expr* t_arg : *t) {
                expr * arg = nullptr;
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
            fi = nullptr;
            if (autil.is_as_array(a)) {
                func_decl* f = autil.get_as_array_func_decl(a);
                // only expand auxiliary definitions that occur once.
                if (can_inline_def(ts, f)) {
                    fi = get_func_interp(f);
                }
            }
            
            if (fi && fi->get_interp()) {
                f = autil.get_as_array_func_decl(a);
                expr_ref_vector sargs(m);
                sort_ref_vector vars(m);
                svector<symbol> var_names;
                for (unsigned i = 0; i < f->get_arity(); ++i) {
                    var_names.push_back(symbol(i));
                    vars.push_back(f->get_domain(f->get_arity() - i - 1));
                }
                new_t = m.mk_lambda(vars.size(), vars.c_ptr(), var_names.c_ptr(), fi->get_interp());
            }
            else if (f->is_skolem() && can_inline_def(ts, f) && (fi = get_func_interp(f)) && 
                     fi->get_interp() && (!ts.partition_ids().find(f, pid) || pid != current_partition)) {
                var_subst vs(m);
                // ? TBD args.reverse();
                new_t = vs(fi->get_interp(), args.size(), args.c_ptr());
            }
#if 0
            else if (is_uninterp_const(a) && !get_const_interp(f)) {
                new_t = get_some_value(f->get_range());
                register_decl(f, new_t);                
            }
#endif
            else {
                new_t = ts.m_rewrite.mk_app(f, args.size(), args.c_ptr());
            }
            
            if (t != new_t.get()) trail.push_back(new_t);
            todo.pop_back();
            cache.insert(t, new_t);
            break;
        }
        default:
            SASSERT(a != nullptr);
            cache.insert(a, a);
            todo.pop_back();
            break;
        }
    }

    ts.m_rewrite(cache[e], new_t);
    return new_t;
}

void model::remove_decls(ptr_vector<func_decl> & decls, func_decl_set const & s) {
    unsigned j = 0;
    for (func_decl* f : decls) {
        if (!s.contains(f)) {
            decls[j++] = f;
        }
    }
    decls.shrink(j);
}


expr_ref model::get_inlined_const_interp(func_decl* f) {
    expr* v = get_const_interp(f);
    if (!v) return expr_ref(nullptr, m);
    top_sort st(m);
    expr_ref result1(v, m);
    expr_ref result2 = cleanup_expr(st, v, UINT_MAX);
    while (result1 != result2) {
        result1 = result2;
        result2 = cleanup_expr(st, result1, UINT_MAX);
    }
    return result2;
}

expr_ref model::operator()(expr* t) {
    return m_mev(t);
}

expr_ref_vector model::operator()(expr_ref_vector const& ts) {
    expr_ref_vector rs(m);
    for (expr* t : ts) rs.push_back((*this)(t));
    return rs;
}

bool model::is_true(expr* t) {
    return m.is_true((*this)(t));
}

bool model::is_false(expr* t) {
    return m.is_false((*this)(t));
}

bool model::is_true(expr_ref_vector const& ts) {
    for (expr* t : ts) if (!is_true(t)) return false;
    return true;
}

void model::reset_eval_cache() {
    m_mev.reset();
}

