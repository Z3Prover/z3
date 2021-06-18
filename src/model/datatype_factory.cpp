/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    datatype_factory.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-11-06.

Revision History:

--*/
#include "model/datatype_factory.h"
#include "model/model_core.h"
#include "ast/ast_pp.h"
#include "ast/expr_functors.h"

datatype_factory::datatype_factory(ast_manager & m, model_core & md):
    struct_factory(m, m.mk_family_id("datatype"), md),
    m_util(m) {
}

expr * datatype_factory::get_some_value(sort * s) {
    if (!m_util.is_datatype(s))
        return m_model.get_some_value(s);
    value_set * set = nullptr;
    if (m_sort2value_set.find(s, set) && !set->empty())
        return *(set->begin());
    func_decl * c = m_util.get_non_rec_constructor(s);
    ptr_vector<expr> args;
    unsigned num  = c->get_arity();
    for (unsigned i = 0; i < num; i++) {
        args.push_back(m_model.get_some_value(c->get_domain(i)));
    }
    expr * r = m_manager.mk_app(c, args);
    register_value(r);
    TRACE("datatype", tout << mk_pp(r, m_util.get_manager()) << "\n";);
    return r;
}

/**
   \brief Return the last fresh (or almost) fresh value of sort s.
*/
expr * datatype_factory::get_last_fresh_value(sort * s) {
    expr * val = nullptr;
    if (m_last_fresh_value.find(s, val)) {
        TRACE("datatype", tout << "cached fresh value: " << mk_pp(val, m_manager) << "\n";);
        return val;
    }
    value_set * set = get_value_set(s);
    if (set->empty())
        val = get_some_value(s);
    else 
        val = *(set->begin());
    if (m_util.is_recursive(s))
        m_last_fresh_value.insert(s, val);
    return val;
}

bool datatype_factory::is_subterm_of_last_value(app* e) {
    expr* last;
    if (!m_last_fresh_value.find(e->get_sort(), last)) {
        return false;
    }
    contains_app contains(m_manager, e);
    bool result = contains(last);
    TRACE("datatype", tout << mk_pp(e, m_manager) << " in " << mk_pp(last, m_manager) << " " << result << "\n";);
    return result;
}

/**
   \brief Create an almost fresh value. If s is recursive, then the result is not 0.
   It also updates m_last_fresh_value
*/
expr * datatype_factory::get_almost_fresh_value(sort * s) {
    if (!m_util.is_datatype(s))
        return m_model.get_some_value(s);
    value_set * set = get_value_set(s);
    if (set->empty()) {
        expr * val = get_some_value(s);
        SASSERT(val);
        if (m_util.is_recursive(s))
            m_last_fresh_value.insert(s, val);
        return val;
    }
    // Traverse constructors, and try to invoke get_fresh_value of one of the arguments (if the argument is not a sibling datatype of s).
    // If the argumet is a sibling datatype of s, then
    // use get_last_fresh_value.
    ptr_vector<func_decl> const & constructors = *m_util.get_datatype_constructors(s);
    for (func_decl * constructor : constructors) {
        expr_ref_vector args(m_manager);
        bool found_fresh_arg = false;
        bool recursive       = false;
        unsigned num            = constructor->get_arity();
        for (unsigned i = 0; i < num; i++) {
            sort * s_arg        = constructor->get_domain(i);
            if (!found_fresh_arg && (!m_util.is_datatype(s_arg) || !m_util.are_siblings(s, s_arg))) {
                expr * new_arg = m_model.get_fresh_value(s_arg);
                if (new_arg != nullptr) {
                    found_fresh_arg = true;
                    args.push_back(new_arg);
                    continue;
                }
            }
            if (!found_fresh_arg && m_util.is_datatype(s_arg) && m_util.are_siblings(s, s_arg)) {
                recursive = true;
                expr * last_fresh = get_last_fresh_value(s_arg);
                args.push_back(last_fresh);
            }
            else {
                expr * some_arg = m_model.get_some_value(s_arg);
                args.push_back(some_arg);
            }
        }
        if (recursive || found_fresh_arg) {
            app * new_value = m_manager.mk_app(constructor, args);
            SASSERT(!found_fresh_arg || !set->contains(new_value));
            register_value(new_value);
            if (m_util.is_recursive(s)) {
                if (is_subterm_of_last_value(new_value)) {
                    new_value = static_cast<app*>(m_last_fresh_value.find(s));
                }
                else {
                    m_last_fresh_value.insert(s, new_value);
                }
            }
            TRACE("datatype", tout << "almost fresh: " << mk_pp(new_value, m_manager) << "\n";);
            return new_value;
        }
    }
    SASSERT(!m_util.is_recursive(s));
    return nullptr;
}


expr * datatype_factory::get_fresh_value(sort * s) {
    if (!m_util.is_datatype(s))
        return m_model.get_fresh_value(s);
    TRACE("datatype", tout << "generating fresh value for: " << s->get_name() << "\n";);
    value_set * set = get_value_set(s);
    // Approach 0) 
    // if no value for s was generated so far, then used get_some_value
    if (set->empty()) {
        expr * val = get_some_value(s);
        if (m_util.is_recursive(s))
            m_last_fresh_value.insert(s, val);
        TRACE("datatype", tout << "0. result: " << mk_pp(val, m_manager) << "\n";);
        return val;
    }
    // Approach 1)
    // Traverse constructors, and try to invoke get_fresh_value of one of the 
    // arguments (if the argument is not a sibling datatype of s).
    // Two datatypes are siblings if they were defined together in the same mutually recursive definition.


    ptr_vector<func_decl> const& constructors = *m_util.get_datatype_constructors(s);
    for (func_decl * constructor : constructors) {
        retry_value:
        expr_ref_vector args(m_manager);
        expr_ref new_value(m_manager);
        bool found_fresh_arg = false;
        unsigned num            = constructor->get_arity();
        for (unsigned i = 0; i < num; i++) {
            sort * s_arg        = constructor->get_domain(i);
            if (!found_fresh_arg && 
                !m_util.is_recursive_array(s_arg) && 
                (!m_util.is_recursive(s) || !m_util.is_datatype(s_arg) || !m_util.are_siblings(s, s_arg))) {
                expr * new_arg = m_model.get_fresh_value(s_arg);
                if (new_arg != nullptr) {
                    found_fresh_arg = true;
                    args.push_back(new_arg);
                    continue;
                }
            }
            expr * some_arg = m_model.get_some_value(s_arg);
            args.push_back(some_arg);
        }

        new_value = m_manager.mk_app(constructor, args);
        CTRACE("datatype", found_fresh_arg && set->contains(new_value), tout << "seen: " << new_value << "\n";);
        if (found_fresh_arg && set->contains(new_value))
            goto retry_value;
        if (!set->contains(new_value)) {
            register_value(new_value);
            if (m_util.is_recursive(s))
                m_last_fresh_value.insert(s, new_value);
            TRACE("datatype", tout << "1. result: " << mk_pp(new_value, m_manager) << "\n";);
            return new_value;
        }
    }
    // Approach 2)
    // For recursive datatypes.
    // search for constructor...
    unsigned num_iterations = 0;
    if (m_util.is_recursive(s)) {
        while (true) {
            ++num_iterations;
            TRACE("datatype", tout << mk_pp(get_last_fresh_value(s), m_manager) << "\n";);
            ptr_vector<func_decl> const & constructors = *m_util.get_datatype_constructors(s);
            for (func_decl * constructor : constructors) {
                expr_ref_vector args(m_manager);
                bool found_sibling   = false;
                unsigned num         = constructor->get_arity();
                TRACE("datatype", tout << "checking constructor: " << constructor->get_name() << "\n";);
                for (unsigned i = 0; i < num; i++) {
                    sort * s_arg        = constructor->get_domain(i);
                    TRACE("datatype", tout << mk_pp(s, m_manager) << " " 
                          << mk_pp(s_arg, m_manager) << " are_siblings " 
                          << m_util.are_siblings(s, s_arg) << "  is_datatype " 
                          << m_util.is_datatype(s_arg) << " found_sibling " 
                          << found_sibling << "\n";);
                    if (!found_sibling && m_util.are_siblings(s, s_arg)) {
                        found_sibling = true;
                        expr * maybe_new_arg = nullptr;
                        if (!m_util.is_datatype(s_arg))
                            maybe_new_arg = m_model.get_fresh_value(s_arg);
                        else if (num_iterations <= 1)
                            maybe_new_arg = get_almost_fresh_value(s_arg);                        
                        else 
                            maybe_new_arg = get_fresh_value(s_arg);
                        if (!maybe_new_arg) {
                            TRACE("datatype", 
                                  tout << "no argument found for " << mk_pp(s_arg, m_manager) << "\n";);
                            maybe_new_arg = m_model.get_some_value(s_arg);
                            found_sibling = false;
                        }
                        SASSERT(maybe_new_arg);
                        args.push_back(maybe_new_arg);
                    }
                    else {
                        expr * some_arg = m_model.get_some_value(s_arg);
                        SASSERT(some_arg);
                        args.push_back(some_arg);
                    }
                }
                if (found_sibling) {
                    expr_ref new_value(m_manager);
                    new_value = m_manager.mk_app(constructor, args);
                    TRACE("datatype", tout << "potential new value: " << mk_pp(new_value, m_manager) << "\n";);
                    m_last_fresh_value.insert(s, new_value);
                    if (!set->contains(new_value)) {
                        register_value(new_value);
                        TRACE("datatype", tout << "2. result: " << mk_pp(new_value, m_manager) << "\n";);
                        return new_value;
                    }
                }
            }
        }
    }
    // Approach 3)
    // for non-recursive datatypes.
    // Search for value that was not created before.
    SASSERT(!m_util.is_recursive(s));
    
    return nullptr;
}

