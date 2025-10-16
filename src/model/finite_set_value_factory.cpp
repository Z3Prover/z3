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
    value_set * set = nullptr;
    SASSERT(u.is_finite_set(s));
    #if 0
    if (m_sort2value_set.find(s, set) && !set->empty()) 
        return *(set->begin());
    #endif
    return u.mk_empty(s);
}

expr * finite_set_value_factory::get_fresh_value(sort * s) {
    sort* elem_sort = nullptr;
    VERIFY(u.is_finite_set(s, elem_sort));
    // Get a fresh value for a finite set sort

    return nullptr;
    #if 0
    value_set * set = get_value_set(s);
    
    // If no values have been generated yet, use get_some_value
    if (set->empty()) {
        auto r = u.mk_empty(s);
        register_value(r);
        return r;
    }
    auto e = md.get_fresh_value(elem_sort);
    if (e) {
        auto r = u.mk_singleton(e);
        register_value(r);
        return r;
    }

    // For finite domains, we may not be able to generate fresh values
    // if all values have been exhausted
    return nullptr;
    #endif
}
