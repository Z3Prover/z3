/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    finite_set_factory.cpp

Abstract:

    Factory for creating finite set values

--*/
#include "model/finite_set_factory.h"
#include "model/model_core.h"

finite_set_factory::finite_set_factory(ast_manager & m, family_id fid, model_core & md):
    struct_factory(m, fid, md),
    u(m) {
}

expr * finite_set_factory::get_some_value(sort * s) {
    // Check if we already have a value for this sort
    value_set * vset = nullptr;
    SASSERT(u.is_finite_set(s));
    if (m_sort2value_set.find(s, vset) && !vset->set.empty()) 
        return *(vset->set.begin());
    return u.mk_empty(s);
}

/**
 * create sets {}, {a}, {b}, {a,b}, {c}, {a,c}, {b,c}, {a,b,c}, {d}, ...
 */
expr * finite_set_factory::get_fresh_value(sort * s) {
    sort* elem_sort = nullptr;
    VERIFY(u.is_finite_set(s, elem_sort));
    
    auto& [set, values] = get_value_set(s);
    
    // Case 1: If no values have been generated yet, return empty set
    if (values.size() == 0) {
        auto r = u.mk_empty(s);
        register_value(r);
        return r;
    }
    
    // Helper lambda to check if a number is a power of 2
    auto is_power_of_2 = [](unsigned n) {
        return n > 0 && (n & (n - 1)) == 0;
    };
    
    // Case 2: If values.size() is a power of 2, create a fresh singleton
    if (is_power_of_2(values.size())) {
        auto e = m_model.get_fresh_value(elem_sort);
        if (!e)
            return nullptr;
        auto r = u.mk_singleton(e);
        register_value(r);
        return r;
    }
    
    // Case 3: Find greatest power of 2 N < values.size() and create union
    // Find the greatest N that is a power of 2 and N < values.size()
    unsigned N = 1;
    while (N * 2 < values.size()) 
        N *= 2;    
    
    auto r = u.mk_union(values.get(values.size() - N), values.get(N));
    register_value(r);
    return r;
}