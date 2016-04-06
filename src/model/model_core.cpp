/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    model_core.cpp

Abstract:

    Base class for models.

Author:

    Leonardo de Moura (leonardo) 2011-04-30.

Revision History:

--*/
#include"model_core.h"

model_core::~model_core() {
    decl2expr::iterator it1  = m_interp.begin();
    decl2expr::iterator end1 = m_interp.end();
    for (; it1 != end1; ++it1) {
        m_manager.dec_ref(it1->m_key);
        m_manager.dec_ref(it1->m_value);
    }

    decl2finterp::iterator it2  = m_finterp.begin();
    decl2finterp::iterator end2 = m_finterp.end();
    for (; it2 != end2; ++it2) {
        m_manager.dec_ref(it2->m_key);
        dealloc(it2->m_value);
    }
}

bool model_core::eval(func_decl* f, expr_ref & r) const {
    if (f->get_arity() == 0) {
        r = get_const_interp(f);
        return r != 0;
    }
    else {
        func_interp * fi = get_func_interp(f);
        if (fi != 0) {
            r = fi->get_interp();
            return r != 0;
        }
        return false;
    }
}

void model_core::register_decl(func_decl * d, expr * v) {
    SASSERT(d->get_arity() == 0);
    decl2expr::obj_map_entry * entry = m_interp.insert_if_not_there2(d, 0);
    if (entry->get_data().m_value == 0) {
        // new entry
        m_decls.push_back(d);
        m_const_decls.push_back(d);
        m_manager.inc_ref(d);
        m_manager.inc_ref(v);
        entry->get_data().m_value = v;
    }
    else {
        // replacing entry
        m_manager.inc_ref(v);
        m_manager.dec_ref(entry->get_data().m_value);
        entry->get_data().m_value = v;
    }
}

void model_core::register_decl(func_decl * d, func_interp * fi) {
    SASSERT(d->get_arity() > 0);
    SASSERT(&fi->m() == &m_manager);
    decl2finterp::obj_map_entry * entry = m_finterp.insert_if_not_there2(d, 0);
    if (entry->get_data().m_value == 0) {
        // new entry
        m_decls.push_back(d);
        m_func_decls.push_back(d);
        m_manager.inc_ref(d);
        entry->get_data().m_value = fi;
    }
    else {
        // replacing entry
        if (fi != entry->get_data().m_value)
            dealloc(entry->get_data().m_value);
        entry->get_data().m_value = fi;
    }
}

