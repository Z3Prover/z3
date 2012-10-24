/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    macro_substitution.cpp

Abstract:

    Mapping from func_decl to quantifiers of the form
             Forall X. f(X) = T[X]
             Forall X. f(X) iff C[X]

Author:

    Leonardo (leonardo) 2012-02-17

Notes:

--*/
#include"macro_substitution.h"
#include"ref_util.h"

typedef obj_map<func_decl, proof*>           func_decl2proof;
typedef obj_map<func_decl, expr_dependency*> func_decl2expr_dependency;

void macro_substitution::init() {
    if (proofs_enabled())
        m_decl2macro_pr  = alloc(func_decl2proof);
    if (unsat_core_enabled())
        m_decl2macro_dep = alloc(func_decl2expr_dependency);
}

macro_substitution::macro_substitution(ast_manager & m):
    m_manager(m),
    m_cores_enabled(false),
    m_proofs_enabled(m.proofs_enabled()) {
    init();
}

macro_substitution::macro_substitution(ast_manager & m, bool cores_enabled):
    m_manager(m),
    m_cores_enabled(cores_enabled),
    m_proofs_enabled(m.proofs_enabled()) {
    init();
}

macro_substitution::macro_substitution(ast_manager & m, bool cores_enabled, bool proofs_enabled):
    m_manager(m),
    m_cores_enabled(cores_enabled),
    m_proofs_enabled(proofs_enabled) {
    SASSERT(!proofs_enabled || m.proofs_enabled());
    init();
}

macro_substitution::~macro_substitution() {
    reset();
}

void macro_substitution::reset() {
    dec_ref_map_key_values(m_manager, m_decl2macro);
    if (proofs_enabled())
        dec_ref_map_values(m_manager, *m_decl2macro_pr);
    if (unsat_core_enabled())
        dec_ref_map_values(m_manager, *m_decl2macro_dep);
}

void macro_substitution::cleanup() {
    reset();
    m_decl2macro.finalize();
    if (proofs_enabled())
        m_decl2macro_pr->finalize();
    if (unsat_core_enabled())
        m_decl2macro_dep->finalize();
}

void macro_substitution::insert(func_decl * f, quantifier * q, proof * pr, expr_dependency * dep) {
    DEBUG_CODE({
        app * body = to_app(q->get_expr());
        SASSERT(m_manager.is_eq(body) || m_manager.is_iff(body));
        expr * lhs = body->get_arg(0);
        expr * rhs = body->get_arg(1);
        SASSERT(is_app_of(lhs, f) || is_app_of(rhs, f));
    });
    obj_map<func_decl, quantifier *>::obj_map_entry * entry = m_decl2macro.insert_if_not_there2(f, 0); 
    if (entry->get_data().m_value == 0) {
        // new entry
        m_manager.inc_ref(f);
        m_manager.inc_ref(q);
        entry->get_data().m_value = q;
        if (proofs_enabled()) {
            SASSERT(!m_decl2macro_pr->contains(f));
            m_decl2macro_pr->insert(f, pr);
            m_manager.inc_ref(pr);
        }
        if (unsat_core_enabled()) {
            SASSERT(!m_decl2macro_dep->contains(f));
            m_decl2macro_dep->insert(f, dep);
            m_manager.inc_ref(dep);
        }
    }
    else {
        // replacing entry
        m_manager.inc_ref(q);
        m_manager.dec_ref(entry->get_data().m_value);
        entry->get_data().m_value = q;
        if (proofs_enabled()) {
            obj_map<func_decl, proof *>::obj_map_entry * entry_pr = m_decl2macro_pr->find_core(f);
            SASSERT(entry_pr != 0);
            m_manager.inc_ref(pr);
            m_manager.dec_ref(entry_pr->get_data().m_value);
            entry_pr->get_data().m_value = pr;
        }
        if (unsat_core_enabled()) {
            obj_map<func_decl, expr_dependency*>::obj_map_entry * entry_dep = m_decl2macro_dep->find_core(f);
            SASSERT(entry_dep != 0);
            m_manager.inc_ref(dep);
            m_manager.dec_ref(entry_dep->get_data().m_value);
            entry_dep->get_data().m_value = dep;
        }
    }
}
 
void macro_substitution::erase(func_decl * f) {
    if (proofs_enabled()) {
        proof * pr = 0;
        if (m_decl2macro_pr->find(f, pr)) {
            m_manager.dec_ref(pr);
            m_decl2macro_pr->erase(f);
        }
    }
    if (unsat_core_enabled()) {
        expr_dependency * dep = 0;
        if (m_decl2macro_dep->find(f, dep)) {
            m_manager.dec_ref(dep);
            m_decl2macro_dep->erase(f);
        }
    }
    quantifier * q = 0;
    if (m_decl2macro.find(f, q)) {
        m_manager.dec_ref(f);
        m_manager.dec_ref(q);
        m_decl2macro.erase(f);
    }
}

void macro_substitution::get_head_def(quantifier * q, func_decl * f, app * & head, expr * & def) {
    app * body = to_app(q->get_expr());
    SASSERT(m_manager.is_eq(body) || m_manager.is_iff(body));
    expr * lhs = to_app(body)->get_arg(0);
    expr * rhs = to_app(body)->get_arg(1);
    SASSERT(is_app_of(lhs, f) || is_app_of(rhs, f));
    SASSERT(!is_app_of(lhs, f) || !is_app_of(rhs, f));
    if (is_app_of(lhs, f)) {
        head = to_app(lhs);
        def  = rhs;
    }
    else {
        head = to_app(rhs);
        def  = lhs;
    }
}

bool macro_substitution::find(func_decl * f, quantifier * & q, proof * & pr) {
    if (m_decl2macro.find(f, q)) {
        if (proofs_enabled())
            m_decl2macro_pr->find(f, pr);
        return true;
    }
    return false;
}

bool macro_substitution::find(func_decl * f, quantifier * & q, proof * & pr, expr_dependency * & dep) {
    if (m_decl2macro.find(f, q)) {
        if (proofs_enabled())
            m_decl2macro_pr->find(f, pr);
        if (unsat_core_enabled())
            m_decl2macro_dep->find(f, dep);
        return true;
    }
    return false;
}


