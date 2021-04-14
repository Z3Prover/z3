/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    proto_model.cpp

Abstract:

    <abstract>

Author:
 
    Leonardo de Moura (leonardo) 2007-03-08.

Revision History:

--*/
#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include "ast/well_sorted.h"
#include "ast/array_decl_plugin.h"
#include "ast/used_symbols.h"
#include "ast/for_each_expr.h"
#include "ast/rewriter/var_subst.h"
#include "model/model_params.hpp"
#include "model/model_v2_pp.h"
#include "smt/proto_model/proto_model.h"


proto_model::proto_model(ast_manager & m, params_ref const & p):
    model_core(m),
    m_eval(*this),
    m_rewrite(m) {
    register_factory(alloc(basic_factory, m));
    m_user_sort_factory = alloc(user_sort_factory, m);
    register_factory(m_user_sort_factory);
    m_model_partial = model_params(p).partial();
}

void proto_model::register_aux_decl(func_decl * d, func_interp * fi) {
    model_core::register_decl(d, fi);
    m_aux_decls.insert(d);
}

void proto_model::register_aux_decl(func_decl * d) {
    m_aux_decls.insert(d);
}

/**
   \brief Set new_fi as the new interpretation for f.
   If f_aux != 0, then assign the old interpretation of f to f_aux.
   If f_aux == 0, then delete the old interpretation of f.

   f_aux is marked as a auxiliary declaration.
*/
void proto_model::reregister_decl(func_decl * f, func_interp * new_fi, func_decl * f_aux) {
    func_interp * fi = get_func_interp(f);
    if (fi == nullptr) {
        register_decl(f, new_fi);
    }
    else {
        if (f_aux != nullptr) {
            register_decl(f_aux, fi);
            m_aux_decls.insert(f_aux);
        }
        else {
            dealloc(fi);
        }
        m_finterp.insert(f, new_fi);
    }
}

expr * proto_model::mk_some_interp_for(func_decl * d) {
    SASSERT(!has_interpretation(d));
    expr * r = get_some_value(d->get_range()); // if t is a function, then it will be the constant function.
    if (d->get_arity() == 0) {
        register_decl(d, r);
    }
    else {
        func_interp * new_fi = alloc(func_interp, m, d->get_arity());
        new_fi->set_else(r);
        register_decl(d, new_fi);
    }
    return r;
}


bool proto_model::eval(expr * e, expr_ref & result, bool model_completion) {
    m_eval.set_model_completion(model_completion);
    m_eval.set_expand_array_equalities(false);
    TRACE("model_evaluator", model_v2_pp(tout, *this, true););
    try {
        m_eval(e, result);
        return true;
    }
    catch (model_evaluator_exception & ex) {
        (void)ex;
        TRACE("model_evaluator", tout << ex.msg() << "\n";);
        return false;
    }
}




/**
   \brief Evaluate the expression e in the current model, and store the result in \c result.
   It returns \c true if succeeded, and false otherwise. If the evaluation fails,
   then r contains a term that is simplified as much as possible using the interpretations
   available in the model.

   When model_completion == true, if the model does not assign an interpretation to a
   declaration it will build one for it. Moreover, partial functions will also be completed.
   So, if model_completion == true, the evaluator never fails if it doesn't contain quantifiers.
*/


/**
   \brief Replace uninterpreted constants occurring in fi->get_else()
   by their interpretations.
*/
void proto_model::cleanup_func_interp(expr_ref_vector& trail, func_interp * fi, func_decl_set & found_aux_fs) {
    if (!fi->is_partial()) {
        expr * fi_else = fi->get_else();    
        fi->set_else(cleanup_expr(trail, fi_else, found_aux_fs));
    }
}

expr* proto_model::cleanup_expr(expr_ref_vector& trail, expr* fi_else, func_decl_set& found_aux_fs) {
    TRACE("model_bug", tout << "cleaning up:\n" << mk_pp(fi_else, m) << "\n";);
    trail.reset();
    obj_map<expr, expr*> cache;
    ptr_buffer<expr, 128> todo;
    ptr_buffer<expr> args;
    todo.push_back(fi_else);
    expr * a;
    expr_ref new_t(m);

    while (!todo.empty()) {
        a = todo.back();
        if (is_uninterp_const(a)) {
            todo.pop_back();
            func_decl * a_decl = to_app(a)->get_decl();
            expr * ai = get_const_interp(a_decl);
            if (ai == nullptr) {
                ai = get_some_value(a_decl->get_range());
                register_decl(a_decl, ai);
            }
            cache.insert(a, ai);
        }
        else {
            switch(a->get_kind()) {
            case AST_APP: {
                app * t = to_app(a);
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
                func_decl * f = t->get_decl();
                if (m_aux_decls.contains(f)) {
                    TRACE("model_bug", tout << f->get_name() << "\n";);
                    found_aux_fs.insert(f);
                }
                new_t = m_rewrite.mk_app(f, args.size(), args.data());                
                if (t != new_t.get())
                    trail.push_back(new_t);
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
    }

    VERIFY(cache.find(fi_else, a));

    return a;
}

void proto_model::remove_aux_decls_not_in_set(ptr_vector<func_decl> & decls, func_decl_set const & s) {
    unsigned j  = 0;
    for (func_decl* f : decls) {
        if (!m_aux_decls.contains(f) || s.contains(f)) {
            decls[j++] = f;
        }
    }
    decls.shrink(j);
}


/**
   \brief Replace uninterpreted constants occurring in the func_interp's get_else()
   by their interpretations.
*/
void proto_model::cleanup() {
    TRACE("model_bug", model_v2_pp(tout, *this););
    func_decl_set found_aux_fs;
    expr_ref_vector trail(m);
    for (auto const& kv : m_finterp) {
        TRACE("model_bug", tout << kv.m_key->get_name() << "\n";);
        func_interp * fi = kv.m_value;
        cleanup_func_interp(trail, fi, found_aux_fs);
    }
    for (unsigned i = 0; i < m_const_decls.size(); ++i) {
        func_decl* d = m_const_decls[i];
        expr* e = m_interp[d].second;
        expr* r = cleanup_expr(trail, e, found_aux_fs);
        if (e != r) {
            register_decl(d, r);
        }        
    }
    // TRACE("model_bug", model_v2_pp(tout, *this););
    // remove auxiliary declarations that are not used.
    if (found_aux_fs.size() != m_aux_decls.size()) {
        remove_aux_decls_not_in_set(m_decls, found_aux_fs);
        remove_aux_decls_not_in_set(m_func_decls, found_aux_fs);

        for (func_decl* faux : m_aux_decls) {
            if (!found_aux_fs.contains(faux)) {
                TRACE("cleanup_bug", tout << "eliminating " << faux->get_name() << " " << faux->get_ref_count() << "\n";);
                unregister_decl(faux);
            }
        }
        m_aux_decls.swap(found_aux_fs);
    }
    TRACE("model_bug", model_v2_pp(tout, *this););
}

value_factory * proto_model::get_factory(family_id fid) {
    return m_factories.get_plugin(fid);
}

void proto_model::freeze_universe(sort * s) {
    SASSERT(m.is_uninterp(s));
    m_user_sort_factory->freeze_universe(s);
}

/**
   \brief Return the known universe of an uninterpreted sort.
*/
obj_hashtable<expr> const & proto_model::get_known_universe(sort * s) const {
    return m_user_sort_factory->get_known_universe(s);
}

ptr_vector<expr> const & proto_model::get_universe(sort * s) const {
    ptr_vector<expr> & tmp = const_cast<proto_model*>(this)->m_tmp;
    tmp.reset();
    obj_hashtable<expr> const & u = get_known_universe(s);
    for (expr * e : u) {
        tmp.push_back(e);
    }
    return tmp;
}

unsigned proto_model::get_num_uninterpreted_sorts() const {
    return m_user_sort_factory->get_num_sorts();
}

sort * proto_model::get_uninterpreted_sort(unsigned idx) const {
    SASSERT(idx < get_num_uninterpreted_sorts());
    return m_user_sort_factory->get_sort(idx);
}

/**
   \brief Return true if the given sort is uninterpreted and has a finite interpretation
   in the model.
*/
bool proto_model::is_finite(sort * s) const {
    return m.is_uninterp(s) && m_user_sort_factory->is_finite(s);
}

expr * proto_model::get_some_value(sort * s) {
    if (m.is_uninterp(s)) {
        return m_user_sort_factory->get_some_value(s);
    }
    else if (value_factory * f = get_factory(s->get_family_id())) {
        return f->get_some_value(s);
    }
    else {
        // there is no factory for the family id, then assume s is uninterpreted.
        return m_user_sort_factory->get_some_value(s);
    }
}

bool proto_model::get_some_values(sort * s, expr_ref & v1, expr_ref & v2) {
    if (m.is_uninterp(s)) {
        return m_user_sort_factory->get_some_values(s, v1, v2);
    }
    else if (value_factory * f = get_factory(s->get_family_id())) {
        return f->get_some_values(s, v1, v2);
    }
    else {
        return false;
    }
}

expr * proto_model::get_fresh_value(sort * s) {
    if (m.is_uninterp(s)) {
        return m_user_sort_factory->get_fresh_value(s);
    }
    else if (value_factory * f = get_factory(s->get_family_id())) {
        return f->get_fresh_value(s);
    }
    else {
        // Use user_sort_factory if the theory has no support for model construnction.
        // This is needed when dummy theories are used for arithmetic or arrays.
        return m_user_sort_factory->get_fresh_value(s);
    }
}

void proto_model::register_value(expr * n) {
    sort * s = n->get_sort();
    if (m.is_uninterp(s)) {
        m_user_sort_factory->register_value(n);
    }
    else {
        family_id fid = s->get_family_id();
        value_factory * f = get_factory(fid);
        if (f)
            f->register_value(n);
    }
}

void proto_model::compress() {
    for (func_decl* f : m_func_decls) {
        func_interp * fi = get_func_interp(f);
        SASSERT(fi != nullptr);
        fi->compress();
    }
}

/**
   \brief Complete the interpretation fi of f if it is partial.
   If f does not have an interpretation in the given model, then this is a noop.
*/
void proto_model::complete_partial_func(func_decl * f, bool use_fresh) {
    func_interp * fi = get_func_interp(f);
    if (fi && fi->is_partial()) {
        expr * else_value;
        if (use_fresh) {
            else_value = get_fresh_value(f->get_range());
        }
        else {
            else_value = fi->get_max_occ_result();
        }
        if (else_value == nullptr)
            else_value = get_some_value(f->get_range());
        fi->set_else(else_value);
    }
}

/**
   \brief Set the (else) field of function interpretations...
*/
void proto_model::complete_partial_funcs(bool use_fresh) {
    if (m_model_partial)
        return;

    // m_func_decls may be "expanded" when we invoke get_some_value.
    // So, we must not use iterators to traverse it.
    for (unsigned i = 0; i < m_func_decls.size(); ++i) {
        complete_partial_func(m_func_decls.get(i), use_fresh);
    }
}

model * proto_model::mk_model() {
    TRACE("proto_model", model_v2_pp(tout << "mk_model\n", *this););
    model * mdl = alloc(model, m);

    for (auto const& kv : m_interp) {
        mdl->register_decl(kv.m_key, kv.m_value.second);
    }

    for (auto const& kv : m_finterp) {
        mdl->register_decl(kv.m_key, kv.m_value);
        m.dec_ref(kv.m_key);
    }

    m_finterp.reset(); // m took the ownership of the func_interp's

    unsigned sz = get_num_uninterpreted_sorts();
    for (unsigned i = 0; i < sz; i++) {
        sort * s = get_uninterpreted_sort(i);
        TRACE("proto_model", tout << "copying uninterpreted sorts...\n" << mk_pp(s, m) << "\n";);
        ptr_vector<expr> const& buf = get_universe(s);
        mdl->register_usort(s, buf.size(), buf.data());
    }

    return mdl;
}

