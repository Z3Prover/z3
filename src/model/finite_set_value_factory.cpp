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
    auto& [set_e, values_e] = get_value_set(elem_sort);
    unsigned next_index = values.size();

    // take the bitmask of next_index to determine which elements to include
    // i.e. if next_index = 13 = 1101_2, then we include elements values_e[0], values_e[2], and values_e[3]
    // new elements for sort s are created on the fly
    int num_shifts = 0;
    auto r = u.mk_empty(s);
    // check the rightmost bit of next_index
    while ( next_index > 0)
    {
        if (next_index & 1) {
            // the element values_e[next_index] is in the set
            expr* element = nullptr;
            if(num_shifts > values_e.size()) {
                // the element we are trying to add does not yet exist
                element = m_model.get_fresh_value(elem_sort);
                if (!element) {
                    // we cannot generate a fresh value for the element sort
                    return nullptr;
                }
                // element is fresh for sort s
                register_value(element);
            }else{
                //retrieve previously generated element
                element = values_e[num_shifts].get();
            }
            r = u.mk_union(r, u.mk_singleton(element));
        }
        num_shifts++;
        next_index = next_index >> 1;
    }
    register_value(r);
    return r;
}