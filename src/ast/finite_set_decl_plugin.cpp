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
#include "ast/polymorphism_util.h"
#include "ast/ast_pp.h"
#include "util/warning.h"

finite_set_decl_plugin::finite_set_decl_plugin():
    m_init(false) {
}

finite_set_decl_plugin::~finite_set_decl_plugin() {
    for (polymorphism::psig* s : m_sigs) 
        dealloc(s);
}

void finite_set_decl_plugin::init() {
    if (m_init) return;
    ast_manager& m = *m_manager;
    array_util autil(m);
    m_init = true;
    
    sort* A = m.mk_type_var(symbol("A"));
    sort* B = m.mk_type_var(symbol("B"));
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
    m_sigs[OP_FINITE_SET_EMPTY]      = alloc(polymorphism::psig, m, "set.empty",      1, 0, nullptr, setA);
    m_sigs[OP_FINITE_SET_SINGLETON]  = alloc(polymorphism::psig, m, "set.singleton",  1, 1, &A, setA);
    m_sigs[OP_FINITE_SET_UNION]      = alloc(polymorphism::psig, m, "set.union",      1, 2, setAsetA, setA);
    m_sigs[OP_FINITE_SET_INTERSECT]  = alloc(polymorphism::psig, m, "set.intersect",  1, 2, setAsetA, setA);
    m_sigs[OP_FINITE_SET_DIFFERENCE]  = alloc(polymorphism::psig, m, "set.difference", 1, 2, setAsetA, setA);
    m_sigs[OP_FINITE_SET_IN]         = alloc(polymorphism::psig, m, "set.in",         1, 2, AsetA, boolT);
    m_sigs[OP_FINITE_SET_SIZE]       = alloc(polymorphism::psig, m, "set.size",       1, 1, &setA, intT);
    m_sigs[OP_FINITE_SET_SUBSET]     = alloc(polymorphism::psig, m, "set.subset",     1, 2, setAsetA, boolT);
    m_sigs[OP_FINITE_SET_MAP]        = alloc(polymorphism::psig, m, "set.map",        2, 2, arrABsetA, setB);
    m_sigs[OP_FINITE_SET_SELECT]     = alloc(polymorphism::psig, m, "set.select",     1, 2, arrABoolsetA, setA);
    m_sigs[OP_FINITE_SET_RANGE]      = alloc(polymorphism::psig, m, "set.range",      0, 2, intintT, setInt);
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

bool finite_set_decl_plugin::is_finite_set(sort* s) const {
    return s->get_family_id() == m_family_id && s->get_decl_kind() == FINITE_SET_SORT;
}

sort * finite_set_decl_plugin::get_element_sort(sort* finite_set_sort) const {
    if (!is_finite_set(finite_set_sort)) {
        return nullptr;
    }
    if (finite_set_sort->get_num_parameters() != 1) {
        return nullptr;
    }
    parameter const* params = finite_set_sort->get_parameters();
    if (!params[0].is_ast() || !is_sort(params[0].get_ast())) {
        return nullptr;
    }
    return to_sort(params[0].get_ast());
}

func_decl * finite_set_decl_plugin::mk_empty(sort* finite_set_sort) {
    parameter param(finite_set_sort);
    if (!is_finite_set(finite_set_sort)) 
        m_manager->raise_exception("set.empty range must be a finite set sort");    
    sort * const * no_domain = nullptr;
    return m_manager->mk_func_decl(m_sigs[OP_FINITE_SET_EMPTY]->m_name, 0u, no_domain, finite_set_sort,
                                   func_decl_info(m_family_id, OP_FINITE_SET_EMPTY, 1, &param));
}

func_decl * finite_set_decl_plugin::mk_finite_set_op(decl_kind k, unsigned arity, sort * const * domain, sort* range) {
    ast_manager& m = *m_manager;
    polymorphism::util poly_util(m);
    sort_ref rng(m);
    poly_util.match(*m_sigs[k], arity, domain, range, rng);
    return m.mk_func_decl(m_sigs[k]->m_name, arity, domain, rng, func_decl_info(m_family_id, k));
}

func_decl * finite_set_decl_plugin::mk_func_decl(decl_kind k, unsigned num_parameters, 
                                                   parameter const * parameters,
                                                   unsigned arity, sort * const * domain, 
                                                   sort * range) {
    init();
    
    switch (k) {
    case OP_FINITE_SET_EMPTY:
        if (!range) {
            if ((num_parameters != 1 || !parameters[0].is_ast() || !is_sort(parameters[0].get_ast()))) {
                m_manager->raise_exception("set.empty requires one sort parameter");
                return nullptr;
            }
            sort* element_sort = to_sort(parameters[0].get_ast());
            // Create finite_set_sort from element_sort
            parameter set_param(element_sort);
            range = m_manager->mk_sort(m_family_id, FINITE_SET_SORT, 1, &set_param);
        }        
        return mk_empty(range);
    case OP_FINITE_SET_SINGLETON:
    case OP_FINITE_SET_UNION:
    case OP_FINITE_SET_INTERSECT:
    case OP_FINITE_SET_DIFFERENCE:
    case OP_FINITE_SET_IN:
    case OP_FINITE_SET_SIZE:
    case OP_FINITE_SET_SUBSET:
    case OP_FINITE_SET_MAP:
    case OP_FINITE_SET_SELECT:
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
    if (is_finite_set(s)) {
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
    return false;
}

bool finite_set_decl_plugin::is_value(app * e) const {
    return is_unique_value(e);
}

bool finite_set_decl_plugin::is_unique_value(app* e) const {
    // Empty set is a value
    return is_app_of(e, m_family_id, OP_FINITE_SET_EMPTY) ||
           (is_app_of(e, m_family_id, OP_FINITE_SET_SINGLETON) && is_unique_value(to_app(e->get_arg(0))));
}

bool finite_set_decl_plugin::are_distinct(app* e1, app* e2) const {
    if (is_unique_value(e1) && is_unique_value(e2))
        return e1 != e2;
    finite_set_recognizers r(get_family_id());   
    if (r.is_empty(e1) && r.is_singleton(e2))
        return true;
    if (r.is_singleton(e1) && r.is_empty(e2))
        return true;
    // TODO: could be extended to cases where we can prove the sets are different by containing one element
    // that the other doesn't contain. Such as (union (singleton a) (singleton b)) and (singleton c) where c is different from a, b.
    return false;
}
