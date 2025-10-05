/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    finite_set_decl_plugin.cpp

Abstract:

    Declaration plugin for finite sets

Author:

    GitHub Copilot Agent 2025

Revision History:

--*/
#include<sstream>
#include "ast/finite_set_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/array_decl_plugin.h"
#include "util/warning.h"

finite_set_decl_plugin::finite_set_decl_plugin():
    m_init(false) {
}

finite_set_decl_plugin::~finite_set_decl_plugin() {
    for (psig* s : m_sigs) 
        dealloc(s);
}

bool finite_set_decl_plugin::is_sort_param(sort* s, unsigned& idx) {
    return
        s->get_name().is_numerical() &&
        (idx = s->get_name().get_num(), true);
}

bool finite_set_decl_plugin::match(ptr_vector<sort>& binding, sort* s, sort* sP) {
    if (s == sP) return true;
    unsigned idx;
    if (is_sort_param(sP, idx)) {
        if (binding.size() <= idx) binding.resize(idx+1);
        if (binding[idx] && (binding[idx] != s)) return false;
        binding[idx] = s;
        return true;
    }

    if (s->get_family_id() == sP->get_family_id() &&
        s->get_decl_kind() == sP->get_decl_kind() &&
        s->get_num_parameters() == sP->get_num_parameters()) {
        for (unsigned i = 0, sz = s->get_num_parameters(); i < sz; ++i) {
            parameter const& p = s->get_parameter(i);
            if (p.is_ast() && is_sort(p.get_ast())) {
                parameter const& p2 = sP->get_parameter(i);
                if (!match(binding, to_sort(p.get_ast()), to_sort(p2.get_ast()))) return false;
            }
        }
        return true;
    }
    else {
        return false;
    }
}

void finite_set_decl_plugin::match(psig& sig, unsigned dsz, sort *const* dom, sort* range, sort_ref& range_out) {
    m_binding.reset();
    ast_manager& m = *m_manager;
    
    if (dsz != sig.m_dom.size()) {
        std::ostringstream strm;
        strm << "Incorrect number of arguments to '" << sig.m_name << "' ";
        strm << "expected " << sig.m_dom.size() << " given " << dsz;
        m.raise_exception(strm.str());
    }
    
    bool is_match = true;
    for (unsigned i = 0; is_match && i < dsz; ++i) {
        SASSERT(dom[i]);
        is_match = match(m_binding, dom[i], sig.m_dom.get(i));
    }
    if (range && is_match) {
        is_match = match(m_binding, range, sig.m_range);
    }
    if (!is_match) {
        std::ostringstream strm;
        strm << "Sort mismatch for function '" << sig.m_name << "'";
        m.raise_exception(strm.str());
    }
    
    // Compute range_out by substituting binding into sig.m_range
    range_out = sig.m_range;
    unsigned idx;
    if (is_sort_param(sig.m_range, idx) && idx < m_binding.size() && m_binding[idx]) {
        range_out = m_binding[idx];
    }
    else if (sig.m_range->get_family_id() == m_family_id && 
             sig.m_range->get_decl_kind() == FINITE_SET_SORT) {
        parameter const& p = sig.m_range->get_parameter(0);
        if (p.is_ast() && is_sort(p.get_ast())) {
            sort* elem_sort = to_sort(p.get_ast());
            if (is_sort_param(elem_sort, idx) && idx < m_binding.size() && m_binding[idx]) {
                parameter new_param(m_binding[idx]);
                range_out = m.mk_sort(m_family_id, FINITE_SET_SORT, 1, &new_param);
            }
        }
    }
}

void finite_set_decl_plugin::init() {
    if (m_init) return;
    ast_manager& m = *m_manager;
    array_util autil(m);
    m_init = true;
    
    sort* A = m.mk_uninterpreted_sort(symbol(0u));
    sort* B = m.mk_uninterpreted_sort(symbol(1u));
    parameter paramA(A);
    parameter paramB(B);
    sort* setA = m.mk_sort(m_family_id, FINITE_SET_SORT, 1, &paramA);
    sort* setB = m.mk_sort(m_family_id, FINITE_SET_SORT, 1, &paramB);
    sort* boolT = m.mk_bool_sort();
    sort* intT = arith_util(m).mk_int();
    parameter paramInt(intT);
    sort* setInt = m.mk_sort(m_family_id, FINITE_SET_SORT, 1, &paramInt);
    sort* arrAB = autil.mk_array_sort(A, B);
    sort* arrABool = autil.mk_array_sort(A, boolT);
    
    sort* setAsetA[2] = { setA, setA };
    sort* AsetA[2] = { A, setA };
    sort* arrABsetA[2] = { arrAB, setA };
    sort* arrABoolsetA[2] = { arrABool, setA };
    sort* intintT[2] = { intT, intT };
    
    m_sigs.resize(LAST_FINITE_SET_OP);
    m_sigs[OP_FINITE_SET_EMPTY]      = alloc(psig, m, "set.empty",      1, 0, nullptr, setA);
    m_sigs[OP_FINITE_SET_SINGLETON]  = alloc(psig, m, "set.singleton",  1, 1, &A, setA);
    m_sigs[OP_FINITE_SET_UNION]      = alloc(psig, m, "set.union",      1, 2, setAsetA, setA);
    m_sigs[OP_FINITE_SET_INTERSECT]  = alloc(psig, m, "set.intersect",  1, 2, setAsetA, setA);
    m_sigs[OP_FINITE_SET_DIFFERENCE]  = alloc(psig, m, "set.difference", 1, 2, setAsetA, setA);
    m_sigs[OP_FINITE_SET_IN]         = alloc(psig, m, "set.in",         1, 2, AsetA, boolT);
    m_sigs[OP_FINITE_SET_SIZE]       = alloc(psig, m, "set.size",       1, 1, &setA, intT);
    m_sigs[OP_FINITE_SET_SUBSET]     = alloc(psig, m, "set.subset",     1, 2, setAsetA, boolT);
    m_sigs[OP_FINITE_SET_MAP]        = alloc(psig, m, "set.map",        2, 2, arrABsetA, setB);
    m_sigs[OP_FINITE_SET_FILTER]     = alloc(psig, m, "set.filter",     1, 2, arrABoolsetA, setA);
    m_sigs[OP_FINITE_SET_RANGE]      = alloc(psig, m, "set.range",      0, 2, intintT, setInt);
}

sort * finite_set_decl_plugin::mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters) {
    if (k == FINITE_SET_SORT) {
        if (num_parameters != 1) {
            m_manager->raise_exception("FiniteSet sort expects exactly one parameter (element sort)");
            return nullptr;
        }
        if (!parameters[0].is_ast() || !is_sort(parameters[0].get_ast())) {
            m_manager->raise_exception("FiniteSet sort parameter must be a sort");
            return nullptr;
        }
        sort * element_sort = to_sort(parameters[0].get_ast());
        sort_size sz = sort_size::mk_very_big();
        sort_info info(m_family_id, FINITE_SET_SORT, sz, num_parameters, parameters);
        return m_manager->mk_sort(symbol("FiniteSet"), info);
    }
    m_manager->raise_exception("unknown finite set sort");
    return nullptr;
}

sort * finite_set_decl_plugin::get_element_sort(sort* finite_set_sort) const {
    if (finite_set_sort->get_family_id() != m_family_id ||
        finite_set_sort->get_decl_kind() != FINITE_SET_SORT) {
        return nullptr;
    }
    parameter const* params = finite_set_sort->get_parameters();
    if (!params[0].is_ast() || !is_sort(params[0].get_ast())) {
        return nullptr;
    }
    return to_sort(params[0].get_ast());
}

func_decl * finite_set_decl_plugin::mk_empty(sort* element_sort) {
    parameter param(element_sort);
    sort * finite_set_sort = m_manager->mk_sort(m_family_id, FINITE_SET_SORT, 1, &param);
    sort * const * no_domain = nullptr;
    return m_manager->mk_func_decl(m_sigs[OP_FINITE_SET_EMPTY]->m_name, 0u, no_domain, finite_set_sort,
                                   func_decl_info(m_family_id, OP_FINITE_SET_EMPTY, 1, &param));
}

func_decl * finite_set_decl_plugin::mk_finite_set_op(decl_kind k, unsigned arity, sort * const * domain, sort* range) {
    ast_manager& m = *m_manager;
    sort_ref rng(m);
    match(*m_sigs[k], arity, domain, range, rng);
    return m.mk_func_decl(m_sigs[k]->m_name, arity, domain, rng, func_decl_info(m_family_id, k));
}

func_decl * finite_set_decl_plugin::mk_func_decl(decl_kind k, unsigned num_parameters, 
                                                   parameter const * parameters,
                                                   unsigned arity, sort * const * domain, 
                                                   sort * range) {
    init();
    
    switch (k) {
    case OP_FINITE_SET_EMPTY:
        if (num_parameters != 1 || !parameters[0].is_ast() || !is_sort(parameters[0].get_ast())) {
            m_manager->raise_exception("set.empty requires one sort parameter");
            return nullptr;
        }
        return mk_empty(to_sort(parameters[0].get_ast()));
    case OP_FINITE_SET_SINGLETON:
    case OP_FINITE_SET_UNION:
    case OP_FINITE_SET_INTERSECT:
    case OP_FINITE_SET_DIFFERENCE:
    case OP_FINITE_SET_IN:
    case OP_FINITE_SET_SIZE:
    case OP_FINITE_SET_SUBSET:
    case OP_FINITE_SET_MAP:
    case OP_FINITE_SET_FILTER:
    case OP_FINITE_SET_RANGE:
        return mk_finite_set_op(k, arity, domain, range);
    default:
        return nullptr;
    }
}

void finite_set_decl_plugin::get_op_names(svector<builtin_name>& op_names, symbol const & logic) {
    init();
    for (unsigned i = 0; i < m_sigs.size(); ++i) {
        if (m_sigs[i])
            op_names.push_back(builtin_name(m_sigs[i]->m_name.str(), i));
    }
}

void finite_set_decl_plugin::get_sort_names(svector<builtin_name>& sort_names, symbol const & logic) {
    sort_names.push_back(builtin_name("FiniteSet", FINITE_SET_SORT));
}

expr * finite_set_decl_plugin::get_some_value(sort * s) {
    if (s->get_family_id() == m_family_id && s->get_decl_kind() == FINITE_SET_SORT) {
        // Return empty set for the given sort
        sort* element_sort = get_element_sort(s);
        if (element_sort) {
            parameter param(element_sort);
            return m_manager->mk_app(m_family_id, OP_FINITE_SET_EMPTY, 1, &param, 0, nullptr);
        }
    }
    return nullptr;
}

bool finite_set_decl_plugin::is_fully_interp(sort * s) const {
    return s->get_family_id() == m_family_id && s->get_decl_kind() == FINITE_SET_SORT;
}

bool finite_set_decl_plugin::is_value(app * e) const {
    // Empty set is a value
    return is_app_of(e, m_family_id, OP_FINITE_SET_EMPTY);
}

bool finite_set_decl_plugin::is_unique_value(app* e) const {
    // Empty set is a unique value for its sort
    return is_value(e);
}
