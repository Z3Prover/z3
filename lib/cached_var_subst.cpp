/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    cached_var_subst.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2009-01-23.

Revision History:

--*/
#include"cached_var_subst.h"

bool cached_var_subst::key_eq_proc::operator()(cached_var_subst::key * k1, cached_var_subst::key * k2) const {
    if (k1->m_qa != k2->m_qa)
        return false;
    if (k1->m_num_bindings != k2->m_num_bindings)
        return false;
    for (unsigned i = 0; i < k1->m_num_bindings; i++) 
        if (k1->m_bindings[i] != k2->m_bindings[i])
            return false;
    return true;
}

cached_var_subst::cached_var_subst(ast_manager & m):
    m_proc(m),
    m_refs(m) {
}

void cached_var_subst::reset() {
    m_refs.reset();
    m_instances.reset();
    m_region.reset();
    m_new_keys.reset();
}

void cached_var_subst::operator()(quantifier * qa, unsigned num_bindings, smt::enode * const * bindings, expr_ref & result) {
    m_new_keys.reserve(num_bindings+1, 0);
    key * new_key = m_new_keys[num_bindings];
    if (new_key == 0)
        new_key = static_cast<key*>(m_region.allocate(sizeof(key) + sizeof(expr*)*num_bindings));

    new_key->m_qa           = qa;
    new_key->m_num_bindings = num_bindings;
    for (unsigned i = 0; i < num_bindings; i++) 
        new_key->m_bindings[i] = bindings[i]->get_owner();
    
    instances::entry * entry = m_instances.insert_if_not_there2(new_key, 0);
    if (entry->get_data().m_key != new_key) {
        SASSERT(entry->get_data().m_value != 0);
        // entry was already there
        m_new_keys[num_bindings] = new_key; // recycle key
        result = entry->get_data().m_value;
        return;
    }
    
    m_proc(qa->get_expr(), new_key->m_num_bindings, new_key->m_bindings, result);
    // cache result
    entry->get_data().m_value = result;

    // remove key from cache
    m_new_keys[num_bindings] = 0;
    
    // increment reference counters
    m_refs.push_back(qa);
    for (unsigned i = 0; i < new_key->m_num_bindings; i++)
        m_refs.push_back(new_key->m_bindings[i]);
    m_refs.push_back(result);
}


 
