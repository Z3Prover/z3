/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    model.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2011-04-30.

Revision History:

--*/
#include"model.h"
#include"ast_pp.h"
#include"ast_ll_pp.h"
#include"var_subst.h"
#include"array_decl_plugin.h"
#include"well_sorted.h"
#include"used_symbols.h"
#include"model_evaluator.h"

model::model(ast_manager & m):
    model_core(m) {
}

model::~model() {
    sort2universe::iterator it3  = m_usort2universe.begin();
    sort2universe::iterator end3 = m_usort2universe.end();
    for (; it3 != end3; ++it3) {
        m_manager.dec_ref(it3->m_key);
        m_manager.dec_array_ref(it3->m_value->size(), it3->m_value->c_ptr());
        dealloc(it3->m_value);
    }
}



void model::copy_const_interps(model const & source) {
    decl2expr::iterator it1  = source.m_interp.begin();
    decl2expr::iterator end1 = source.m_interp.end();
    for (; it1 != end1; ++it1) {
        register_decl(it1->m_key, it1->m_value);
    }
}

void model::copy_func_interps(model const & source) {
    decl2finterp::iterator it2  = source.m_finterp.begin();
    decl2finterp::iterator end2 = source.m_finterp.end();
    for (; it2 != end2; ++it2) {
        register_decl(it2->m_key, it2->m_value->copy());
    }
}

void model::copy_usort_interps(model const & source) {
    sort2universe::iterator it3  = source.m_usort2universe.begin();
    sort2universe::iterator end3 = source.m_usort2universe.end();
    for (; it3 != end3; ++it3) {
        register_usort(it3->m_key, it3->m_value->size(), it3->m_value->c_ptr());
    }
}

model * model::copy() const {
    model * m = alloc(model, m_manager);

    m->copy_const_interps(*this);
    m->copy_func_interps(*this);
    m->copy_usort_interps(*this);

    return m;
}

// Remark: eval is for backward compatibility. We should use model_evaluator.
bool model::eval(expr * e, expr_ref & result, bool model_completion) {
    model_evaluator ev(*this);
    ev.set_model_completion(model_completion);
    try {
        ev(e, result);
        return true;
    }
    catch (model_evaluator_exception & ex) {
        (void)ex;
        TRACE("model_evaluator", tout << ex.msg() << "\n";);
        return false;
    }
}

struct model::value_proc : public some_value_proc {
    model & m_model;
    value_proc(model & m):m_model(m) {}
    virtual expr * operator()(sort * s) {
        ptr_vector<expr> * u = 0;
        if (m_model.m_usort2universe.find(s, u)) {
            if (u->size() > 0)
                return u->get(0);
        }
        return 0;
    }
};

expr * model::get_some_value(sort * s) {
    value_proc p(*this);
    return m_manager.get_some_value(s, &p);
}

ptr_vector<expr> const & model::get_universe(sort * s) const {
    ptr_vector<expr> * u = 0;
    m_usort2universe.find(s, u);
    SASSERT(u != 0);
    return *u;
}

bool model::has_uninterpreted_sort(sort * s) const {
    ptr_vector<expr> * u = 0;
    m_usort2universe.find(s, u);
    return u != 0;
}

unsigned model::get_num_uninterpreted_sorts() const {
    return m_usorts.size();
}

sort * model::get_uninterpreted_sort(unsigned idx) const {
    return m_usorts[idx];
}

void model::register_usort(sort * s, unsigned usize, expr * const * universe) {
    sort2universe::obj_map_entry * entry = m_usort2universe.insert_if_not_there2(s, 0);
    m_manager.inc_array_ref(usize, universe);
    if (entry->get_data().m_value == 0) {
        // new entry
        m_usorts.push_back(s);
        m_manager.inc_ref(s);
        ptr_vector<expr> * new_u = alloc(ptr_vector<expr>);
        new_u->append(usize, universe);
        entry->get_data().m_value = new_u;
    }
    else {
        // updating
        ptr_vector<expr> * u = entry->get_data().m_value;
        SASSERT(u);
        m_manager.dec_array_ref(u->size(), u->c_ptr());
        u->append(usize, universe);
    }
}

model * model::translate(ast_translation & translator) const {
    model * res = alloc(model, translator.to());

    // Translate const interps
    decl2expr::iterator it1  = m_interp.begin();
    decl2expr::iterator end1 = m_interp.end();
    for (; it1 != end1; ++it1) {
        res->register_decl(translator(it1->m_key), translator(it1->m_value));
    }

    // Translate func interps
    decl2finterp::iterator it2  = m_finterp.begin();
    decl2finterp::iterator end2 = m_finterp.end();
    for (; it2 != end2; ++it2) {
        func_interp * fi = it2->m_value;
        res->register_decl(translator(it2->m_key), fi->translate(translator));
    }

    // Translate usort interps
    sort2universe::iterator it3  = m_usort2universe.begin();
    sort2universe::iterator end3 = m_usort2universe.end();
    for (; it3 != end3; ++it3) {
        ptr_vector<expr> new_universe;
        for (unsigned i=0; i<it3->m_value->size(); i++)
            new_universe.push_back(translator(it3->m_value->get(i)));
        res->register_usort(translator(it3->m_key),
                            new_universe.size(),
                            new_universe.c_ptr());
    }

    return res;
}

