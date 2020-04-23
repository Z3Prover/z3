/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    struct_factory.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-11-06.

Revision History:

--*/
#include "model/struct_factory.h"
#include "model/model_core.h"

struct_factory::value_set * struct_factory::get_value_set(sort * s) {
    value_set * set = nullptr;
    if (!m_sort2value_set.find(s, set)) {
        set = alloc(value_set);
        m_sort2value_set.insert(s, set);
        m_sorts.push_back(s);
        m_sets.push_back(set);
    }
    SASSERT(set != 0);
    return set;
}

struct_factory::struct_factory(ast_manager & m, family_id fid, model_core & md):
    value_factory(m, fid),
    m_model(md),
    m_values(m),
    m_sorts(m) {
}

struct_factory::~struct_factory() {
    std::for_each(m_sets.begin(), m_sets.end(), delete_proc<value_set>());
}

void struct_factory::register_value(expr * new_value) {
    sort * s        = m_manager.get_sort(new_value);
    value_set * set = get_value_set(s);
    if (!set->contains(new_value)) {
        m_values.push_back(new_value);
        set->insert(new_value);
    }
}

bool struct_factory::get_some_values(sort * s, expr_ref & v1, expr_ref & v2) {
    value_set * set = get_value_set(s);
    switch (set->size()) {
    case 0:
        v1 = get_fresh_value(s);
        v2 = get_fresh_value(s);
        return v1 != 0 && v2 != 0;
    case 1:
        v1 = get_some_value(s);
        v2 = get_fresh_value(s);
        return v2 != 0;
    default:
        obj_hashtable<expr>::iterator it = set->begin();
        v1 = *it;
        ++it;
        v2 = *it;
        return true;
    }
}






