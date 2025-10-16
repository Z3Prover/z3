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
    u(m) {
}

expr * finite_set_value_factory::get_some_value(sort * s) {
    // Check if we already have a value for this sort
    value_set * vset = nullptr;
    SASSERT(u.is_finite_set(s));
    if (m_sort2value_set.find(s, vset) && !vset->set.empty()) 
        return *(vset->set.begin());
    return u.mk_empty(s);
}

expr * finite_set_value_factory::get_fresh_value(sort * s) {
    sort* elem_sort = nullptr;
    VERIFY(u.is_finite_set(s, elem_sort));
    // Get a fresh value for a finite set sort

    auto& [set, values] = get_value_set(s);
    
    // If no values have been generated yet, use get_some_value
    if (set.empty()) {
        auto r = u.mk_empty(s);
        register_value(r);
        return r;
    }
    auto e = m_model.get_fresh_value(elem_sort);
    if (e) {
        auto r = u.mk_singleton(e);
        register_value(e); // register e so we can access the finite domain within this class
        register_value(r);
        return r;
    }
    auto& [set_e, values_e] = get_value_set(elem_sort);
    unsigned next_index = values.size();
    SASSERT(next_index >= 1 + values_e.size());  // we already generated the empty set and all singletons   

    // Course Task of 10-16-25:
    // For finite domains, we may not be able to generate fresh values
    // if all values have been exhausted
    // create sets based on next_index
    // assume that values_e contains all the values of the element sort
    // and they have already been generated.
    // Figure out if we are creating two, three, or more element sets
    // and map next_index into the elements in a uniqe way.
    return nullptr;
}