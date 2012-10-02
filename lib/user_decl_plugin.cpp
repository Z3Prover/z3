/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    user_decl_plugin.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2010-05-22.

Revision History:

--*/
#include"user_decl_plugin.h"
#include"warning.h"

user_decl_plugin::user_decl_plugin() {
}
    
void user_decl_plugin::finalize() {
    m_manager->dec_array_ref(m_kind2func.size(), m_kind2func.c_ptr());
    m_manager->dec_array_ref(m_kind2sort.size(), m_kind2sort.c_ptr());
}

decl_plugin * user_decl_plugin::mk_fresh() {
    user_decl_plugin * p = alloc(user_decl_plugin);
    // TODO copy sorts and other goodness
    return p;
}

sort * user_decl_plugin::mk_sort(symbol const & name) {
    unsigned kind = m_kind2sort.size();
    sort * s      = m_manager->mk_sort(name, sort_info(m_family_id, kind));
    m_kind2sort.push_back(s);
    m_manager->inc_ref(s);
    if (!name.is_numerical()) {
        m_sort_names.push_back(builtin_name(name.bare_str(), static_cast<decl_kind>(kind)));
    }
    return s;
}
    
func_decl * user_decl_plugin::mk_func_decl(symbol const & name, unsigned arity, sort * const * domain, sort * range) {
    unsigned kind = m_kind2func.size();
    func_decl * f = m_manager->mk_func_decl(name, arity, domain, range, func_decl_info(m_family_id, kind));
    m_kind2func.push_back(f);
    m_manager->inc_ref(f);
    if (!name.is_numerical()) {
        m_op_names.push_back(builtin_name(name.bare_str(), static_cast<decl_kind>(kind)));
    }
    return f;
}
    
func_decl * user_decl_plugin::mk_value_decl(symbol const & name, sort * s) {
    func_decl * f = mk_func_decl(name, 0, 0, s);
    m_values.insert(f);
    return f;
}
    
sort * user_decl_plugin::mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters) {
    if (num_parameters > 0) {
        throw default_exception("invalid user theory sort");
        return 0;
    }
    return m_kind2sort.get(k, 0);
}
    
func_decl * user_decl_plugin::mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters, 
                                           unsigned arity, sort * const * domain, sort * range) {
    func_decl * f = m_kind2func.get(k, 0);
    if (num_parameters > 0 || f == 0) {
        throw default_exception("invalid user theory function operator");
        return 0;
    }
    return f;
}
    
bool user_decl_plugin::is_value(app * v) const {
    return m_values.contains(v->get_decl()); 
}

bool user_decl_plugin::is_value(func_decl * f) const {
    return m_values.contains(f); 
}
    
void user_decl_plugin::get_op_names(svector<builtin_name> & op_names, symbol const & logic) {
    op_names.append(m_op_names);
}
    
void user_decl_plugin::get_sort_names(svector<builtin_name> & sort_names, symbol const & logic) {
    sort_names.append(m_sort_names);
}

