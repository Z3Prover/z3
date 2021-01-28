/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    cached_var_subst.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2009-01-23.

Revision History:

--*/
#include "ast/rewriter/cached_var_subst.h"
#include "ast/rewriter/rewriter_def.h"

bool cached_var_subst::key_eq_proc::operator()(cached_var_subst::key * k1, cached_var_subst::key * k2) const {
    if (k1->m_qa != k2->m_qa)
        return false;
    if (k1->m_num_bindings != k2->m_num_bindings)
        return false;
    for (unsigned i = 0; i < k1->m_num_bindings; i++)
        if (k1->m_bindings[i] != k2->m_bindings[i])
            return false;
    return true;
}

cached_var_subst::cached_var_subst(ast_manager & _m):
    m(_m),
    m_proc(m),
    m_refs(m) {
}

void cached_var_subst::reset() {
    m_refs.reset();
    m_instances.reset();
    m_region.reset();
    m_new_keys.reset();
    m_key = nullptr;
}

expr** cached_var_subst::operator()(quantifier* qa, unsigned num_bindings) {
    m_new_keys.reserve(num_bindings+1, 0);
    m_key = m_new_keys[num_bindings];
    if (m_key == nullptr)
        m_key = static_cast<key*>(m_region.allocate(sizeof(key) + sizeof(expr*)*num_bindings));
    m_key->m_qa           = qa;
    m_key->m_num_bindings = num_bindings;
    return m_key->m_bindings;
}


expr_ref cached_var_subst::operator()() {
    expr_ref result(m);

    auto* entry = m_instances.insert_if_not_there3(m_key, nullptr);
    unsigned num_bindings = m_key->m_num_bindings;
    if (entry->get_data().m_key != m_key) {
        SASSERT(entry->get_data().m_value != 0);
        // entry was already there
        m_new_keys[num_bindings] = m_key; // recycle key
        result = entry->get_data().m_value;
        SCTRACE("bindings", is_trace_enabled("coming_from_quant"), tout << "(cache)\n";
                for (unsigned i = 0; i < num_bindings; i++) 
                    if (m_key->m_bindings[i]) 
                        tout << i << ": " << mk_ismt2_pp(m_key->m_bindings[i], result.m()) << ";\n";
                tout.flush(););
        return result;
    }

    SASSERT(entry->get_data().m_value == 0);
    try {
        result = m_proc(m_key->m_qa->get_expr(), m_key->m_num_bindings, m_key->m_bindings);
    }
    catch (...) {
        // CMW: The var_subst reducer was interrupted and m_instances is
        // in an inconsistent state; we need to remove (m_key, 0).
        m_instances.remove(m_key);
        throw; 
    }

    // cache result
    entry->get_data().m_value = result;

    // remove key from cache
    m_new_keys[num_bindings] = nullptr;

    // increment reference counters
    m_refs.push_back(m_key->m_qa);
    for (unsigned i = 0; i < m_key->m_num_bindings; i++)
        m_refs.push_back(m_key->m_bindings[i]);
    m_refs.push_back(result);
    return result;
}
