/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    expr_substitution.cpp

Abstract:

    expr -> expr substitution

Author:

    Leonardo (leonardo) 2011-04-29

Notes:

--*/
#include"expr_substitution.h"
#include"ref_util.h"

typedef obj_map<expr, proof*> expr2proof;
typedef obj_map<expr, expr_dependency*> expr2expr_dependency;

void expr_substitution::init() {

    if (proofs_enabled())
        m_subst_pr = alloc(expr2proof);
    if (unsat_core_enabled())
        m_subst_dep = alloc(expr2expr_dependency);
}

expr_substitution::expr_substitution(ast_manager & m):
    m_manager(m),
    m_cores_enabled(false),
    m_proofs_enabled(m.proofs_enabled()) {
    init();
}

expr_substitution::expr_substitution(ast_manager & m, bool core_enabled):
    m_manager(m),
    m_cores_enabled(core_enabled),
    m_proofs_enabled(m.proofs_enabled()) {
    init();
}

expr_substitution::expr_substitution(ast_manager & m, bool core_enabled, bool proofs_enabled):
    m_manager(m),
    m_cores_enabled(core_enabled),
    m_proofs_enabled(proofs_enabled) {
    SASSERT(!proofs_enabled || m.proofs_enabled());
    init();
}

expr_substitution::~expr_substitution() {
    reset();
}

void expr_substitution::insert(expr * c, expr * def, proof * def_pr, expr_dependency * def_dep) {
    obj_map<expr, expr*>::obj_map_entry * entry = m_subst.insert_if_not_there2(c, 0); 
    if (entry->get_data().m_value == 0) {
        // new entry
        m_manager.inc_ref(c);
        m_manager.inc_ref(def);
        entry->get_data().m_value = def;
        if (proofs_enabled()) {
            SASSERT(!m_subst_pr->contains(c));
            m_subst_pr->insert(c, def_pr);
            m_manager.inc_ref(def_pr);
        }
        if (unsat_core_enabled()) {
            SASSERT(!m_subst_dep->contains(c));
            m_subst_dep->insert(c, def_dep);
            m_manager.inc_ref(def_dep);
        }
    }
    else {
        // replacing entry
        m_manager.inc_ref(def);
        m_manager.dec_ref(entry->get_data().m_value);
        entry->get_data().m_value = def;
        if (proofs_enabled()) {
            obj_map<expr, proof*>::obj_map_entry * entry_pr = m_subst_pr->find_core(c);
            SASSERT(entry_pr != 0);
            m_manager.inc_ref(def_pr);
            m_manager.dec_ref(entry_pr->get_data().m_value);
            entry_pr->get_data().m_value = def_pr;
        }
        if (unsat_core_enabled()) {
            obj_map<expr, expr_dependency*>::obj_map_entry * entry_dep = m_subst_dep->find_core(c);
            SASSERT(entry_dep != 0);
            m_manager.inc_ref(def_dep);
            m_manager.dec_ref(entry_dep->get_data().m_value);
            entry_dep->get_data().m_value = def_dep;
        }
    }
}

void expr_substitution::erase(expr * c) {
    if (proofs_enabled()) {
        proof * pr = 0;
        if (m_subst_pr->find(c, pr)) {
            m_manager.dec_ref(pr);
            m_subst_pr->erase(c);
        }
    }
    if (unsat_core_enabled()) {
        expr_dependency * dep = 0;
        if (m_subst_dep->find(c, dep)) {
            m_manager.dec_ref(dep);
            m_subst_dep->erase(c);
        }
    }
    expr * def = 0;
    if (m_subst.find(c, def)) {
        m_manager.dec_ref(c);
        m_manager.dec_ref(def);
        m_subst.erase(c);
    }
}

bool expr_substitution::find(expr * c, expr * & def, proof * & def_pr) {
    if (m_subst.find(c, def)) {
        if (proofs_enabled())
            m_subst_pr->find(c, def_pr);
        return true;
    }
    return false;
}

bool expr_substitution::find(expr * c, expr * & def, proof * & def_pr, expr_dependency * & def_dep) {
    if (m_subst.find(c, def)) {
        if (proofs_enabled())
            m_subst_pr->find(c, def_pr);
        if (unsat_core_enabled())
            m_subst_dep->find(c, def_dep);
        return true;
    }
    return false;
}

bool expr_substitution::contains(expr * s) {
    return m_subst.contains(s);
}

void expr_substitution::reset() {
    dec_ref_map_key_values(m_manager, m_subst);
    if (proofs_enabled())
        dec_ref_map_values(m_manager, *m_subst_pr);
    if (unsat_core_enabled())
        dec_ref_map_values(m_manager, *m_subst_dep);
}

void expr_substitution::cleanup() {
    reset();
    m_subst.finalize();
    if (proofs_enabled())
        m_subst_pr->finalize();
    if (unsat_core_enabled())
        m_subst_dep->finalize();
}
