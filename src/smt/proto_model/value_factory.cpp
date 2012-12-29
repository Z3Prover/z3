/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    value_factory.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-10-28.

Revision History:

--*/

#include"value_factory.h"

value_factory::value_factory(ast_manager & m, family_id fid):
    m_manager(m), 
    m_fid(fid) {
}

value_factory::~value_factory() {
}

basic_factory::basic_factory(ast_manager & m):
    value_factory(m, m.get_basic_family_id()) {
}

expr * basic_factory::get_some_value(sort * s) {
    if (m_manager.is_bool(s))
        return m_manager.mk_false();
    return 0;
}

bool basic_factory::get_some_values(sort * s, expr_ref & v1, expr_ref & v2) {
    if (m_manager.is_bool(s)) {
        v1 = m_manager.mk_false();
        v2 = m_manager.mk_true();
        return true;
    }
    return false;
}
    
expr * basic_factory::get_fresh_value(sort * s) {
    return 0;
}

user_sort_factory::user_sort_factory(ast_manager & m): 
    simple_factory<unsigned>(m, m.mk_family_id("user-sort")) {
}

void user_sort_factory::freeze_universe(sort * s) {
    if (!m_finite.contains(s)) {
        value_set * set = 0;
        m_sort2value_set.find(s, set);
        if (!m_sort2value_set.find(s, set) || set->m_values.empty()) {
            // we cannot freeze an empty universe.
            get_some_value(s); // add one element to the universe...
        }
        SASSERT(m_sort2value_set.find(s, set) && set != 0 && !set->m_values.empty());
        m_finite.insert(s);
    }
}

obj_hashtable<expr> const & user_sort_factory::get_known_universe(sort * s) const {
    value_set * set = 0;
    if (m_sort2value_set.find(s, set)) {
        return set->m_values;
    }
    return m_empty_universe;
}

expr * user_sort_factory::get_some_value(sort * s) {
    if (is_finite(s)) {
        value_set * set = 0;
        m_sort2value_set.find(s, set);
        SASSERT(set != 0);
        SASSERT(!set->m_values.empty());
        return *(set->m_values.begin());
    }
    return simple_factory<unsigned>::get_some_value(s);
}

bool user_sort_factory::get_some_values(sort * s, expr_ref & v1, expr_ref & v2) {
    if (is_finite(s)) {
        value_set * set = 0;
        if (m_sort2value_set.find(s, set) && set->m_values.size() >= 2) {
            obj_hashtable<expr>::iterator it = set->m_values.begin();
            v1 = *it;
            ++it;
            v2 = *it;
            return true;
        }
        return false;
    }
    return simple_factory<unsigned>::get_some_values(s, v1, v2);
}

expr * user_sort_factory::get_fresh_value(sort * s) {
    if (is_finite(s))
        return 0;
    return simple_factory<unsigned>::get_fresh_value(s);
}

void user_sort_factory::register_value(expr * n) {
    SASSERT(!is_finite(m_manager.get_sort(n)));
    simple_factory<unsigned>::register_value(n);
}

app * user_sort_factory::mk_value_core(unsigned const & val, sort * s) {
    return m_manager.mk_model_value(val, s);
}
