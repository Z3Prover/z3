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
#include"datatype_factory.h"
#include"proto_model.h"
#include"ast_pp.h"
#include"ast_ll_pp.h"

datatype_factory::datatype_factory(ast_manager & m, proto_model & md):
    struct_factory(m, m.get_family_id("datatype"), md),
    m_util(m) {
}

expr * datatype_factory::get_some_value(sort * s) {
    value_set * set = 0;
    if (m_sort2value_set.find(s, set) && !set->empty())
        return *(set->begin());
    func_decl * c = m_util.get_non_rec_constructor(s);
    ptr_vector<expr> args;
    unsigned num  = c->get_arity();
    for (unsigned i = 0; i < num; i++) {
        args.push_back(m_model.get_some_value(c->get_domain(i)));
    }
    expr * r = m_manager.mk_app(c, args.size(), args.c_ptr());
    register_value(r);
    TRACE("datatype_factory", tout << mk_pp(r, m_util.get_manager()) << "\n";);
    return r;
}

/**
   \brief Return the last fresh (or almost) fresh value of sort s.
*/
expr * datatype_factory::get_last_fresh_value(sort * s) {
    expr * val = 0;
    if (m_last_fresh_value.find(s, val))
        return val;
    value_set * set = get_value_set(s);
    if (set->empty())
        val = get_some_value(s);
    else 
        val = *(set->begin());
    if (m_util.is_recursive(s))
        m_last_fresh_value.insert(s, val);
    return val;
}

/**
   \brief Create an almost fresh value. If s is recursive, then the result is not 0.
   It also updates m_last_fresh_value
*/
expr * datatype_factory::get_almost_fresh_value(sort * s) {
    value_set * set = get_value_set(s);
    if (set->empty()) {
        expr * val = get_some_value(s);
        if (m_util.is_recursive(s))
            m_last_fresh_value.insert(s, val);
        return val;
    }
    // Traverse constructors, and try to invoke get_fresh_value of one of the arguments (if the argument is not a sibling datatype of s).
    // If the argumet is a sibling datatype of s, then
    // use get_last_fresh_value.
    ptr_vector<func_decl> const * constructors = m_util.get_datatype_constructors(s);
    ptr_vector<func_decl>::const_iterator it   = constructors->begin();
    ptr_vector<func_decl>::const_iterator end  = constructors->end();
    for (; it != end; ++it) {
        func_decl * constructor = *it;
        expr_ref_vector args(m_manager);
        bool found_fresh_arg = false;
        bool recursive       = false;
        unsigned num            = constructor->get_arity();
        for (unsigned i = 0; i < num; i++) {
            sort * s_arg        = constructor->get_domain(i);
            if (!found_fresh_arg && (!m_util.is_datatype(s_arg) || !m_util.are_siblings(s, s_arg))) {
                expr * new_arg = m_model.get_fresh_value(s_arg);
                if (new_arg != 0) {
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
            expr * new_value = m_manager.mk_app(constructor, args.size(), args.c_ptr());
            SASSERT(!found_fresh_arg || !set->contains(new_value));
            register_value(new_value);
            if (m_util.is_recursive(s))
                m_last_fresh_value.insert(s, new_value);
            return new_value;
        }
    }
    SASSERT(!m_util.is_recursive(s));
    return 0;
}


expr * datatype_factory::get_fresh_value(sort * s) {
    TRACE("datatype_factory", tout << "generating fresh value for: " << s->get_name() << "\n";);
    value_set * set = get_value_set(s);
    // Approach 0) 
    // if no value for s was generated so far, then used get_some_value
    if (set->empty()) {
        expr * val = get_some_value(s);
        if (m_util.is_recursive(s))
            m_last_fresh_value.insert(s, val);
        TRACE("datatype_factory", tout << "0. result: " << mk_pp(val, m_manager) << "\n";);
        return val;
    }
    // Approach 1)
    // Traverse constructors, and try to invoke get_fresh_value of one of the 
    // arguments (if the argument is not a sibling datatype of s).
    // Two datatypes are siblings if they were defined together in the same mutually recursive definition.
    ptr_vector<func_decl> const * constructors = m_util.get_datatype_constructors(s);
    ptr_vector<func_decl>::const_iterator it   = constructors->begin();
    ptr_vector<func_decl>::const_iterator end  = constructors->end();
    for (; it != end; ++it) {
        func_decl * constructor = *it;
        expr_ref_vector args(m_manager);
        bool found_fresh_arg = false;
        unsigned num            = constructor->get_arity();
        for (unsigned i = 0; i < num; i++) {
            sort * s_arg        = constructor->get_domain(i);
            if (!found_fresh_arg && (!m_util.is_recursive(s) || !m_util.is_datatype(s_arg) || !m_util.are_siblings(s, s_arg))) {
                expr * new_arg = m_model.get_fresh_value(s_arg);
                if (new_arg != 0) {
                    found_fresh_arg = true;
                    args.push_back(new_arg);
                    continue;
                }
            }
            expr * some_arg = m_model.get_some_value(s_arg);
            args.push_back(some_arg);
        }
        expr_ref new_value(m_manager);
        new_value = m_manager.mk_app(constructor, args.size(), args.c_ptr());
        CTRACE("datatype_factory", found_fresh_arg && set->contains(new_value), tout << mk_pp(new_value, m_manager) << "\n";);
        SASSERT(!found_fresh_arg || !set->contains(new_value));
        if (!set->contains(new_value)) {
            register_value(new_value);
            if (m_util.is_recursive(s))
                m_last_fresh_value.insert(s, new_value);
            TRACE("datatype_factory", tout << "1. result: " << mk_pp(new_value, m_manager) << "\n";);
            return new_value;
        }
    }
    // Approach 2)
    // For recursive datatypes.
    // search for constructor...
    if (m_util.is_recursive(s)) {
        while(true) {
            TRACE("datatype_factory", tout << mk_pp(get_last_fresh_value(s), m_manager) << "\n";);
            ptr_vector<func_decl> const * constructors = m_util.get_datatype_constructors(s);
            ptr_vector<func_decl>::const_iterator it   = constructors->begin();
            ptr_vector<func_decl>::const_iterator end  = constructors->end();
            for (; it != end; ++it) {
                func_decl * constructor = *it;
                expr_ref_vector args(m_manager);
                bool found_sibling   = false;
                unsigned num         = constructor->get_arity();
                for (unsigned i = 0; i < num; i++) {
                    sort * s_arg        = constructor->get_domain(i);
                    if (!found_sibling && m_util.is_datatype(s_arg) && m_util.are_siblings(s, s_arg)) {
                        found_sibling = true;
                        expr * maybe_new_arg = get_almost_fresh_value(s_arg);
                        args.push_back(maybe_new_arg);
                    }
                    else {
                        expr * some_arg = m_model.get_some_value(s_arg);
                        args.push_back(some_arg);
                    }
                }
                if (found_sibling) {
                    expr_ref new_value(m_manager);
                    new_value = m_manager.mk_app(constructor, args.size(), args.c_ptr());
                    m_last_fresh_value.insert(s, new_value);
                    if (!set->contains(new_value)) {
                        register_value(new_value);
                        TRACE("datatype_factory", tout << "2. result: " << mk_pp(new_value, m_manager) << "\n";);
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
    
    return 0;
}

