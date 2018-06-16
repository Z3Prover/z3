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
#include "model/model.h"
#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include "ast/rewriter/var_subst.h"
#include "ast/array_decl_plugin.h"
#include "ast/well_sorted.h"
#include "ast/used_symbols.h"
#include "model/model_evaluator.h"

model::model(ast_manager & m):
    model_core(m),
    m_mev(*this) {
}

model::~model() {
    for (auto & kv : m_usort2universe) {
        m_manager.dec_ref(kv.m_key);
        m_manager.dec_array_ref(kv.m_value->size(), kv.m_value->c_ptr());
        dealloc(kv.m_value);
    }
}



void model::copy_const_interps(model const & source) {
    for (auto const& kv : source.m_interp) {
        register_decl(kv.m_key, kv.m_value);
    }
}

void model::copy_func_interps(model const & source) {
    for (auto const& kv : source.m_finterp) 
        register_decl(kv.m_key, kv.m_value->copy());
}

void model::copy_usort_interps(model const & source) {
    for (auto const& kv : source.m_usort2universe) 
        register_usort(kv.m_key, kv.m_value->size(), kv.m_value->c_ptr());
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
    expr * operator()(sort * s) override {
        ptr_vector<expr> * u = nullptr;
        if (m_model.m_usort2universe.find(s, u)) {
            if (u->size() > 0)
                return u->get(0);
        }
        return nullptr;
    }
};

expr * model::get_some_value(sort * s) {
    value_proc p(*this);
    return m_manager.get_some_value(s, &p);
}

ptr_vector<expr> const & model::get_universe(sort * s) const {
    ptr_vector<expr> * u = nullptr;
    m_usort2universe.find(s, u);
    SASSERT(u != 0);
    return *u;
}

bool model::has_uninterpreted_sort(sort * s) const {
    ptr_vector<expr> * u = nullptr;
    m_usort2universe.find(s, u);
    return u != nullptr;
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
    for (auto const& kv : m_interp) 
        res->register_decl(translator(kv.m_key), translator(kv.m_value));

    // Translate func interps
    for (auto const& kv : m_finterp) {
        func_interp * fi = kv.m_value;
        res->register_decl(translator(kv.m_key), fi->translate(translator));
    }

    // Translate usort interps
    for (auto const& kv : m_usort2universe) {
        ptr_vector<expr> new_universe;
        for (unsigned i=0; i < kv.m_value->size(); i++)
            new_universe.push_back(translator(kv.m_value->get(i)));
        res->register_usort(translator(kv.m_key),
                            new_universe.size(),
                            new_universe.c_ptr());
    }

    return res;
}

expr_ref model::operator()(expr* t) {
    return m_mev(t);
}

expr_ref_vector model::operator()(expr_ref_vector const& ts) {
    expr_ref_vector rs(m());
    for (expr* t : ts) rs.push_back((*this)(t));
    return rs;
}

bool model::is_true(expr* t) {
    return m().is_true((*this)(t));
}

bool model::is_false(expr* t) {
    return m().is_false((*this)(t));
}

bool model::is_true(expr_ref_vector const& ts) {
    for (expr* t : ts) if (!is_true(t)) return false;
    return true;
}

void model::reset_eval_cache() {
    m_mev.reset();
}

