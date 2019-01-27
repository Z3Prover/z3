/*++
Copyright (c) 2007 Microsoft Corporation

Module Name:

    expr_map.cpp

Abstract:

    Mapping from expressions to expressions + proofs. This mapping
    is used to cache simplification results. 
    For every entry [e1->(e2, p)] we have that p is a proof that (= e1 e2).

Author:

    Leonardo (leonardo) 2008-01-03

Notes:

--*/
#include "ast/expr_map.h"
#include "util/dec_ref_util.h"

expr_map::expr_map(ast_manager & m):
    m_manager(m),
    m_store_proofs(m.proofs_enabled()) {
}

expr_map::expr_map(ast_manager & m, bool store_proofs):
    m_manager(m),
    m_store_proofs(store_proofs) {
}

expr_map::~expr_map() {
    reset();
}

void expr_map::insert(expr * k, expr * d, proof * p) {  
    m_manager.inc_ref(d);
    obj_map<expr, expr*>::obj_map_entry * entry = m_expr2expr.find_core(k);
    if (entry != nullptr) {
        m_manager.dec_ref(entry->get_data().m_value);
        entry->get_data().m_value = d;
        if (m_store_proofs) {
            m_manager.inc_ref(p);
            obj_map<expr, proof*>::obj_map_entry * entry_pr = m_expr2pr.find_core(k);
            SASSERT(entry_pr != 0);
            m_manager.dec_ref(entry_pr->get_data().m_value);
            entry_pr->get_data().m_value = p;
        }
    }
    else {
        m_manager.inc_ref(k);
        m_expr2expr.insert(k, d);
        if (m_store_proofs) {
            m_manager.inc_ref(p);
            m_expr2pr.insert(k, p);
        }
    }
}

void expr_map::get(expr * k, expr * & d, proof * & p) const {
    if (m_expr2expr.find(k, d)) {
        p = nullptr;
        if (m_store_proofs)
            m_expr2pr.find(k, p);
    }
}

void expr_map::erase(expr * k) {
    expr * v;
    if (m_expr2expr.find(k, v)) {
        m_expr2expr.erase(k);
        m_manager.dec_ref(v);
        if (m_store_proofs) {
            proof * pr = nullptr;
            m_expr2pr.find(k, pr);
            m_expr2pr.erase(k);
            m_manager.dec_ref(pr);
        }
        m_manager.dec_ref(k);
    }
}

void expr_map::reset() {
    dec_ref_values(m_manager, m_expr2pr);
    dec_ref_key_values(m_manager, m_expr2expr);
}

void expr_map::flush() {
    reset();
    m_expr2expr.finalize();
    m_expr2pr.finalize();
}
