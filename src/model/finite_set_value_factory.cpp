/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    finite_set_value_factory.cpp

Abstract:

    Factory for creating finite set values

--*/
#include "model/finite_set_value_factory.h"
#include "model/model_core.h"

finite_set_value_factory::finite_set_value_factory(ast_manager & m, family_id fid, model_core & md):
    struct_factory(m, fid, md),
    m_util(m) {
}

expr * finite_set_value_factory::get_some_value(sort * s) {
    // Check if we already have a value for this sort
    value_set * set = nullptr;
    SASSERT(u.is_finite_set(s));
    if (m_sort2value_set.find(s, set) && !set->empty()) 
        return *(set->begin());

    // For sets, return an empty set
    if (m_util.is_array(s)) {
        expr * empty = m_util.mk_empty_set(s);
        register_value(empty);
        return empty;
    }

    return nullptr;
}

expr * finite_set_value_factory::get_fresh_value(sort * s) {
    // Get a fresh value for a finite set sort
    value_set * set = get_value_set(s);
    
    // If no values have been generated yet, use get_some_value
    if (set->empty()) 
        return get_some_value(s);

    // For sets represented as arrays
    if (m_util.is_array(s)) {
        // Get the element sort (domain of the array)
        sort * elem_sort = get_array_domain(s, 0);
        
        // Try to get a fresh value from the element domain
        expr * fresh_elem = m_model.get_fresh_value(elem_sort);
        if (fresh_elem != nullptr) {
            // Create a singleton set with the fresh element
            // Start with an empty set and add the element
            expr * empty = m_util.mk_empty_set(s);
            expr * args[3] = { empty, fresh_elem, m_manager.mk_true() };
            expr * singleton = m_util.mk_store(3, args);
            register_value(singleton);
            return singleton;
        }
    }

    // For finite domains, we may not be able to generate fresh values
    // if all values have been exhausted
    return nullptr;
}
