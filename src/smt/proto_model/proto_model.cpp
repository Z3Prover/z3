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
#include"proto_model.h"
#include"model_params.hpp"
#include"ast_pp.h"
#include"ast_ll_pp.h"
#include"var_subst.h"
#include"array_decl_plugin.h"
#include"well_sorted.h"
#include"used_symbols.h"
#include"model_v2_pp.h"
#include"basic_simplifier_plugin.h"

proto_model::proto_model(ast_manager & m, simplifier & s, params_ref const & p):
    model_core(m),
    m_asts(m),
    m_simplifier(s),
    m_afid(m.mk_family_id(symbol("array"))) {
    register_factory(alloc(basic_factory, m));
    m_user_sort_factory = alloc(user_sort_factory, m);
    register_factory(m_user_sort_factory);
    
    m_model_partial = model_params(p).partial();
}

void proto_model::reset_finterp() {
     decl2finterp::iterator it  = m_finterp.begin();
     decl2finterp::iterator end = m_finterp.end();
     for (; it != end; ++it) {
         dealloc(it->m_value);
     }
}

proto_model::~proto_model() {
    reset_finterp();
}

void proto_model::register_decl(func_decl * d, expr * v) {
    SASSERT(d->get_arity() == 0);
    if (m_interp.contains(d)) {
        DEBUG_CODE({
            expr * old_v = 0;
            m_interp.find(d, old_v);
            SASSERT(old_v == v);
        });
        return;
    }
    SASSERT(!m_interp.contains(d));
    m_decls.push_back(d);
    m_asts.push_back(d);
    m_asts.push_back(v);
    m_interp.insert(d, v);
    m_const_decls.push_back(d);
}

void proto_model::register_decl(func_decl * d, func_interp * fi, bool aux) {
    SASSERT(d->get_arity() > 0);
    SASSERT(!m_finterp.contains(d));
    m_decls.push_back(d);
    m_asts.push_back(d);
    m_finterp.insert(d, fi);
    m_func_decls.push_back(d);
    if (aux)
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
    if (fi == 0) {
        register_decl(f, new_fi);
    }
    else {
        if (f_aux != 0) {
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
        func_interp * new_fi = alloc(func_interp, m_manager, d->get_arity());
        new_fi->set_else(r);
        register_decl(d, new_fi);
    }
    return r;
}

// Auxiliary function for computing fi(args[0], ..., args[fi.get_arity() - 1]).
// The result is stored in result.
// Return true if succeeded, and false otherwise.
// It uses the simplifier s during the computation.
bool eval(func_interp & fi, simplifier & s, expr * const * args, expr_ref & result) {
    bool actuals_are_values = true;
    
    if (fi.num_entries() != 0) {
        for (unsigned i = 0; actuals_are_values && i < fi.get_arity(); i++) {
            actuals_are_values = fi.m().is_value(args[i]);
        }
    }

    func_entry * entry = fi.get_entry(args);
    if (entry != 0) {
        result = entry->get_result();
        return true;
    }
    
    TRACE("func_interp", tout << "failed to find entry for: "; 
          for(unsigned i = 0; i < fi.get_arity(); i++) 
             tout << mk_pp(args[i], fi.m()) << " "; 
          tout << "\nis partial: " << fi.is_partial() << "\n";);
    
    if (!fi.eval_else(args, result)) {
        return false;
    }
    
    if (actuals_are_values && fi.args_are_values()) {
        // cheap case... we are done
        return true;
    }

    // build symbolic result... the actuals may be equal to the args of one of the entries.
    basic_simplifier_plugin * bs = static_cast<basic_simplifier_plugin*>(s.get_plugin(fi.m().get_basic_family_id()));
    for (unsigned k = 0; k < fi.num_entries(); k++) {
        func_entry const * curr = fi.get_entry(k);
        SASSERT(!curr->eq_args(fi.m(), fi.get_arity(), args));
        if (!actuals_are_values || !curr->args_are_values()) {
            expr_ref_buffer eqs(fi.m());
            unsigned i = fi.get_arity();
            while (i > 0) {
                --i;
                expr_ref new_eq(fi.m());
                bs->mk_eq(curr->get_arg(i), args[i], new_eq);
                eqs.push_back(new_eq);
            }
            SASSERT(eqs.size() == fi.get_arity());
            expr_ref new_cond(fi.m());
            bs->mk_and(eqs.size(), eqs.c_ptr(), new_cond);
            bs->mk_ite(new_cond, curr->get_result(), result, result);
        }
    }
    return true;
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
bool proto_model::eval(expr * e, expr_ref & result, bool model_completion) {
    bool is_ok = true;
    SASSERT(is_well_sorted(m_manager, e));
    TRACE("model_eval", tout << mk_pp(e, m_manager) << "\n";
          tout << "sort: " << mk_pp(m_manager.get_sort(e), m_manager) << "\n";);
    
    obj_map<expr, expr*> eval_cache;
    expr_ref_vector trail(m_manager);
    sbuffer<std::pair<expr*, expr*>, 128> todo;
    ptr_buffer<expr> args;
    expr * null = static_cast<expr*>(0);
    todo.push_back(std::make_pair(e, null));
    

    expr * a;
    expr * expanded_a;
    while (!todo.empty()) {
        std::pair<expr *, expr *> & p = todo.back();
        a          = p.first;
        expanded_a = p.second;
        if (expanded_a != 0) {
            expr * r = 0;
            eval_cache.find(expanded_a, r);
            SASSERT(r != 0);
            todo.pop_back();
            eval_cache.insert(a, r);
            TRACE("model_eval", 
                  tout << "orig:\n" << mk_pp(a, m_manager) << "\n";
                  tout << "after beta reduction:\n" << mk_pp(expanded_a, m_manager) << "\n";
                  tout << "new:\n" << mk_pp(r, m_manager) << "\n";);
        }
        else {
            switch(a->get_kind()) {
            case AST_APP: {
                app * t = to_app(a);
                bool visited = true;
                args.reset();
                unsigned num_args = t->get_num_args();
                for (unsigned i = 0; i < num_args; ++i) {
                    expr * arg = 0;
                    if (!eval_cache.find(t->get_arg(i), arg)) {
                        visited = false;
                        todo.push_back(std::make_pair(t->get_arg(i), null));
                    }
                    else {
                        args.push_back(arg);
                    }
                }
                if (!visited) {
                    continue;
                }
                SASSERT(args.size() == t->get_num_args());
                expr_ref new_t(m_manager);
                func_decl * f   = t->get_decl();
                
                if (!has_interpretation(f)) {
                    // the model does not assign an interpretation to f.
                    SASSERT(new_t.get() == 0);
                    if (f->get_family_id() == null_family_id) {
                        if (model_completion) {
                            // create an interpretation for f.
                            new_t = mk_some_interp_for(f);
                        }
                        else {
                            TRACE("model_eval", tout << f->get_name() << " is uninterpreted\n";);
                            is_ok = false;
                        }
                    }
                    if (new_t.get() == 0) {
                        // t is interpreted or model completion is disabled.
                        m_simplifier.mk_app(f, num_args, args.c_ptr(), new_t);
                        TRACE("model_eval", tout << mk_pp(t, m_manager) << " -> " << new_t << "\n";);
                        trail.push_back(new_t);
                        if (!is_app(new_t) || to_app(new_t)->get_decl() != f) {
                            // if the result is not of the form (f ...), then assume we must simplify it.
                            expr * new_new_t = 0;
                            if (!eval_cache.find(new_t.get(), new_new_t)) {
                                todo.back().second = new_t;
                                todo.push_back(std::make_pair(new_t, null));
                                continue;
                            }
                            else {
                                new_t = new_new_t;
                            }
                        }
                    }
                }
                else {
                    // the model has an interpretaion for f.
                    if (num_args == 0) {
                        // t is a constant
                        new_t = get_const_interp(f);
                    }
                    else {
                        // t is a function application
                        SASSERT(new_t.get() == 0);
                        // try to use function graph first
                        func_interp * fi = get_func_interp(f);
                        SASSERT(fi->get_arity() == num_args);
                        expr_ref r1(m_manager);
                        // fi may be partial...
                        if (!::eval(*fi, m_simplifier, args.c_ptr(), r1)) {
                            SASSERT(fi->is_partial()); // fi->eval only fails when fi is partial.
                            if (model_completion) {
                                expr * r = get_some_value(f->get_range()); 
                                fi->set_else(r);
                                SASSERT(!fi->is_partial());
                                new_t = r;
                            }
                            else {
                                // f is an uninterpreted function, there is no need to use m_simplifier.mk_app
                                new_t = m_manager.mk_app(f, num_args, args.c_ptr());
                                trail.push_back(new_t);
                                TRACE("model_eval", tout << f->get_name() << " is uninterpreted\n";);
                                is_ok = false;
                            }
                        }
                        else {
                            SASSERT(r1);
                            trail.push_back(r1);
                            TRACE("model_eval", tout << mk_pp(a, m_manager) << "\nevaluates to: " << r1 << "\n";);
                            expr * r2 = 0;
                            if (!eval_cache.find(r1.get(), r2)) {
                                todo.back().second = r1;
                                todo.push_back(std::make_pair(r1, null));
                                continue;
                            }
                            else {
                                new_t = r2;
                            }
                        }
                    }
                }
                TRACE("model_eval", 
                      tout << "orig:\n" << mk_pp(t, m_manager) << "\n";
                      tout << "new:\n" << mk_pp(new_t, m_manager) << "\n";);
                todo.pop_back();
                SASSERT(new_t.get() != 0);
                eval_cache.insert(t, new_t);
                break;
            }
            case AST_VAR:  
                SASSERT(a != 0);
                eval_cache.insert(a, a);
                todo.pop_back();
                break;
            case AST_QUANTIFIER: 
                TRACE("model_eval", tout << "found quantifier\n" << mk_pp(a, m_manager) << "\n";);
                is_ok = false; // evaluator does not handle quantifiers.
                SASSERT(a != 0);
                eval_cache.insert(a, a);
                todo.pop_back();
                break;
            default:
                UNREACHABLE();
                break;
            }
        }
    }

    if (!eval_cache.find(e, a)) {
        TRACE("model_eval", tout << "FAILED e: " << mk_bounded_pp(e, m_manager) << "\n";);
        UNREACHABLE();
    }

    result = a;
    TRACE("model_eval", 
          ast_ll_pp(tout << "original:  ", m_manager, e);
          ast_ll_pp(tout << "evaluated: ", m_manager, a);
          ast_ll_pp(tout << "reduced:   ", m_manager, result.get());
          tout << "sort: " << mk_pp(m_manager.get_sort(e), m_manager) << "\n";
          ); 
    SASSERT(is_well_sorted(m_manager, result.get()));
    return is_ok;
}

/**
   \brief Replace uninterpreted constants occurring in fi->get_else()
   by their interpretations.
*/
void proto_model::cleanup_func_interp(func_interp * fi, func_decl_set & found_aux_fs) {
    if (fi->is_partial())
        return;
    expr * fi_else = fi->get_else();
    TRACE("model_bug", tout << "cleaning up:\n" << mk_pp(fi_else, m_manager) << "\n";);

    obj_map<expr, expr*> cache;
    expr_ref_vector trail(m_manager);
    ptr_buffer<expr, 128> todo;
    ptr_buffer<expr> args;
    todo.push_back(fi_else);

    expr * a;
    while (!todo.empty()) {
        a = todo.back();
        if (is_uninterp_const(a)) {
            todo.pop_back();
            func_decl * a_decl = to_app(a)->get_decl();
            expr * ai = get_const_interp(a_decl);
            if (ai == 0) {
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
                unsigned num_args = t->get_num_args();
                for (unsigned i = 0; i < num_args; ++i) {
                    expr * arg = 0;
                    if (!cache.find(t->get_arg(i), arg)) {
                        visited = false;
                        todo.push_back(t->get_arg(i));
                    }
                    else {
                        args.push_back(arg);
                    }
                }
                if (!visited) {
                    continue;
                }
                func_decl * f = t->get_decl();
                if (m_aux_decls.contains(f))
                    found_aux_fs.insert(f);
                expr_ref new_t(m_manager);
                m_simplifier.mk_app(f, num_args, args.c_ptr(), new_t);
                if (t != new_t.get())
                    trail.push_back(new_t);
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
    }

    if (!cache.find(fi_else, a)) {
        UNREACHABLE();
    }
    
    fi->set_else(a);
}

void proto_model::remove_aux_decls_not_in_set(ptr_vector<func_decl> & decls, func_decl_set const & s) {
    unsigned sz = decls.size();
    unsigned i  = 0;
    unsigned j  = 0;
    for (; i < sz; i++) {
        func_decl * f = decls[i];
        if (!m_aux_decls.contains(f) || s.contains(f)) {
            decls[j] = f;
            j++;
        }
    }
    decls.shrink(j);
}


/**
   \brief Replace uninterpreted constants occurring in the func_interp's get_else()
   by their interpretations.
*/
void proto_model::cleanup() {
    func_decl_set found_aux_fs;
    decl2finterp::iterator it  = m_finterp.begin();
    decl2finterp::iterator end = m_finterp.end();
    for (; it != end; ++it) {
        func_interp * fi = (*it).m_value;
        cleanup_func_interp(fi, found_aux_fs);
    }
    
    // remove auxiliary declarations that are not used.
    if (found_aux_fs.size() != m_aux_decls.size()) {
        remove_aux_decls_not_in_set(m_decls, found_aux_fs);
        remove_aux_decls_not_in_set(m_func_decls, found_aux_fs);
        
        func_decl_set::iterator it2  = m_aux_decls.begin();
        func_decl_set::iterator end2 = m_aux_decls.end();
        for (; it2 != end2; ++it2) {
            func_decl * faux = *it2;
            if (!found_aux_fs.contains(faux)) {
                TRACE("cleanup_bug", tout << "eliminating " << faux->get_name() << "\n";);
                func_interp * fi = 0;
                m_finterp.find(faux, fi);
                SASSERT(fi != 0);
                m_finterp.erase(faux);
                dealloc(fi);
            }
        }
        m_aux_decls.swap(found_aux_fs);
    }
}

value_factory * proto_model::get_factory(family_id fid) {
    return m_factories.get_plugin(fid);
}

void proto_model::freeze_universe(sort * s) {
    SASSERT(m_manager.is_uninterp(s));
    m_user_sort_factory->freeze_universe(s);
}

/**
   \brief Return the known universe of an uninterpreted sort.
*/
obj_hashtable<expr> const & proto_model::get_known_universe(sort * s) const {
    SASSERT(m_manager.is_uninterp(s));
    return m_user_sort_factory->get_known_universe(s);
}

ptr_vector<expr> const & proto_model::get_universe(sort * s) const {
    ptr_vector<expr> & tmp = const_cast<proto_model*>(this)->m_tmp;
    tmp.reset();
    obj_hashtable<expr> const & u = get_known_universe(s);
    obj_hashtable<expr>::iterator it = u.begin();
    obj_hashtable<expr>::iterator end = u.end();
    for (; it != end; ++it)
        tmp.push_back(*it);
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
    return m_manager.is_uninterp(s) && m_user_sort_factory->is_finite(s);
}

expr * proto_model::get_some_value(sort * s) {
    if (m_manager.is_uninterp(s)) {
        return m_user_sort_factory->get_some_value(s);
    }
    else {
        family_id fid = s->get_family_id();
        value_factory * f = get_factory(fid);
        if (f) 
            return f->get_some_value(s);
        // there is no factory for the family id, then assume s is uninterpreted.
        return m_user_sort_factory->get_some_value(s);
    }
}

bool proto_model::get_some_values(sort * s, expr_ref & v1, expr_ref & v2) {
    if (m_manager.is_uninterp(s)) {
        return m_user_sort_factory->get_some_values(s, v1, v2);
    }
    else {
        family_id fid = s->get_family_id();
        value_factory * f = get_factory(fid);
        if (f) 
            return f->get_some_values(s, v1, v2);
        else
            return false;
    }
}

expr * proto_model::get_fresh_value(sort * s) {
    if (m_manager.is_uninterp(s)) {
        return m_user_sort_factory->get_fresh_value(s);
    }
    else {
        family_id fid = s->get_family_id();    
        value_factory * f = get_factory(fid);
        if (f) 
            return f->get_fresh_value(s);
        else
            // Use user_sort_factory if the theory has no support for model construnction.
            // This is needed when dummy theories are used for arithmetic or arrays.
            return m_user_sort_factory->get_fresh_value(s);
    }
}

void proto_model::register_value(expr * n) {
    sort * s = m_manager.get_sort(n);
    if (m_manager.is_uninterp(s)) {
        m_user_sort_factory->register_value(n);
    }
    else {
        family_id fid = s->get_family_id();
        value_factory * f = get_factory(fid);
        if (f)
            f->register_value(n);
    }
}

bool proto_model::is_array_value(expr * v) const {
    return is_app_of(v, m_afid, OP_AS_ARRAY);
}

void proto_model::compress() {
    ptr_vector<func_decl>::iterator it  = m_func_decls.begin();
    ptr_vector<func_decl>::iterator end = m_func_decls.end();
    for (; it != end; ++it) {
        func_decl * f = *it;
        func_interp * fi = get_func_interp(f);
        SASSERT(fi != 0);
        fi->compress();
    }
}

/**
   \brief Complete the interpretation fi of f if it is partial.
   If f does not have an interpretation in the given model, then this is a noop.
*/
void proto_model::complete_partial_func(func_decl * f) {
    func_interp * fi = get_func_interp(f);
    if (fi && fi->is_partial()) {
        expr * else_value = 0;
#if 0 
        // For UFBV benchmarks, setting the "else" to false is not a good idea.
        // TODO: find a permanent solution. A possibility is to add another option.
        if (m_manager.is_bool(f->get_range())) {
            else_value = m_manager.mk_false();
        }
        else {
            else_value = fi->get_max_occ_result();
            if (else_value == 0)
                else_value = get_some_value(f->get_range());
        }
#else
        else_value = fi->get_max_occ_result();
        if (else_value == 0)
            else_value = get_some_value(f->get_range());
#endif
        fi->set_else(else_value);
    }
}

/**
   \brief Set the (else) field of function interpretations... 
*/
void proto_model::complete_partial_funcs() {
    if (m_model_partial)
        return;

    // m_func_decls may be "expanded" when we invoke get_some_value.
    // So, we must not use iterators to traverse it.
    for (unsigned i = 0; i < m_func_decls.size(); i++) {
        complete_partial_func(m_func_decls[i]);
    }
}

model * proto_model::mk_model() {
    TRACE("proto_model", tout << "mk_model\n"; model_v2_pp(tout, *this););
    model * m = alloc(model, m_manager);

    decl2expr::iterator it1  = m_interp.begin();
    decl2expr::iterator end1 = m_interp.end();
    for (; it1 != end1; ++it1) {
        m->register_decl(it1->m_key, it1->m_value);
    }

    decl2finterp::iterator it2  = m_finterp.begin();
    decl2finterp::iterator end2 = m_finterp.end();
    for (; it2 != end2; ++it2) {
        m->register_decl(it2->m_key, it2->m_value);
    }
    m_finterp.reset(); // m took the ownership of the func_interp's

    unsigned sz = get_num_uninterpreted_sorts();
    for (unsigned i = 0; i < sz; i++) {
        sort * s = get_uninterpreted_sort(i);
        TRACE("proto_model", tout << "copying uninterpreted sorts...\n" << mk_pp(s, m_manager) << "\n";);
        ptr_buffer<expr> buf;
        obj_hashtable<expr> const & u = get_known_universe(s);
        obj_hashtable<expr>::iterator it  = u.begin();
        obj_hashtable<expr>::iterator end = u.end();
        for (; it != end; ++it) {
            buf.push_back(*it);
        }
        m->register_usort(s, buf.size(), buf.c_ptr());
    }

    return m;
}
