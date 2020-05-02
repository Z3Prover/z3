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
#include "model/model_core.h"
#include "ast/ast_pp.h"

model_core::~model_core() {
    for (auto & kv : m_interp) {
        m.dec_ref(kv.m_key);
        m.dec_ref(kv.m_value);
    }

    for (auto & kv : m_finterp) {
        m.dec_ref(kv.m_key);
        dealloc(kv.m_value);
    }
}

bool model_core::eval(func_decl* f, expr_ref & r) const {
    if (f->get_arity() == 0) {
        r = get_const_interp(f);
        return r != 0;
    }
    else {
        func_interp * fi = get_func_interp(f);
        if (fi != nullptr) {
            r = fi->get_interp();
            return r != 0;
        }
        return false;
    }
}

void model_core::register_decl(func_decl * d, expr * v) {
    if (d->get_arity() > 0) {
        func_interp* fi = alloc(func_interp, m, d->get_arity());
        fi->set_else(v);
        register_decl(d, fi);
        return;
    }
    TRACE("model", tout << "register " << d->get_name() << "\n";
          if (v) tout << mk_pp(v, m) << "\n";
          );
    auto& value = m_interp.insert_if_not_there(d, nullptr);
    if (value == nullptr) {
        // new entry
        m_decls.push_back(d);
        m_const_decls.push_back(d);
        m.inc_ref(d);
        m.inc_ref(v);
        value = v;
    }
    else {
        // replacing entry
        m.inc_ref(v);
        m.dec_ref(value);
        value = v;
    }
}

void model_core::register_decl(func_decl * d, func_interp * fi) {
    TRACE("model", tout << "register " << d->get_name() << "\n";);
    SASSERT(d->get_arity() > 0);
    SASSERT(&fi->m() == &m);
    auto& value = m_finterp.insert_if_not_there(d, nullptr);
    if (value == nullptr) {
        // new entry
        m_decls.push_back(d);
        m_func_decls.push_back(d);
        m.inc_ref(d);
        value = fi;
    }
    else {
        // replacing entry
        if (fi != value)
            dealloc(value);
        value = fi;
    }
}

void model_core::unregister_decl(func_decl * d) {
    decl2expr::obj_map_entry * ec = m_interp.find_core(d);
    if (ec) {
        auto k = ec->get_data().m_key;
        auto v = ec->get_data().m_value;
        m_interp.remove(d);
        m_const_decls.erase(d);
        m.dec_ref(k);
        m.dec_ref(v);
        return;
    }

    decl2finterp::obj_map_entry * ef = m_finterp.find_core(d);
    if (ef) {
        auto k = ef->get_data().m_key;
        auto v = ef->get_data().m_value;
        m_finterp.remove(d);
        m_func_decls.erase(d);
        m.dec_ref(k);
        dealloc(v);
    }
}
