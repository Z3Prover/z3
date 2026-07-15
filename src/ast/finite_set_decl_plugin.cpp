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
#include <sstream>
#include "ast/finite_set_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/array_decl_plugin.h"
#include "ast/polymorphism_util.h"
#include "ast/ast_pp.h"
#include "util/warning.h"

finite_set_decl_plugin::finite_set_decl_plugin() {
    m_names.resize(LAST_FINITE_SET_OP, nullptr);
    m_names[OP_FINITE_SET_EMPTY] = "set.empty";
    m_names[OP_FINITE_SET_SINGLETON] = "set.singleton";
    m_names[OP_FINITE_SET_UNION] = "set.union";
    m_names[OP_FINITE_SET_INTERSECT] = "set.intersect";
    m_names[OP_FINITE_SET_DIFFERENCE] = "set.difference";
    m_names[OP_FINITE_SET_IN] = "set.in";
    m_names[OP_FINITE_SET_SIZE] = "set.size";
    m_names[OP_FINITE_SET_SUBSET] = "set.subset";
    m_names[OP_FINITE_SET_MAP] = "set.map";
    m_names[OP_FINITE_SET_FILTER] = "set.filter";
    m_names[OP_FINITE_SET_RANGE] = "set.range";
    m_names[OP_FINITE_SET_EXT] = "set.diff";
    m_names[OP_FINITE_SET_MAP_INVERSE] = "set.map.inverse";
    m_names[OP_FINITE_SET_UNIQUE_SET] = "set.unique";
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
    sort *arrABBsetA[3] = {arrAB, B, setA};
    
    m_sigs.resize(LAST_FINITE_SET_OP);
    m_sigs[OP_FINITE_SET_EMPTY]      = alloc(polymorphism::psig, m, m_names[OP_FINITE_SET_EMPTY],      1, 0, nullptr, setA);
    m_sigs[OP_FINITE_SET_SINGLETON]  = alloc(polymorphism::psig, m, m_names[OP_FINITE_SET_SINGLETON], 1, 1, &A, setA);
    m_sigs[OP_FINITE_SET_UNION]      = alloc(polymorphism::psig, m, m_names[OP_FINITE_SET_UNION], 1, 2, setAsetA, setA);
    m_sigs[OP_FINITE_SET_INTERSECT]  = alloc(polymorphism::psig, m, m_names[OP_FINITE_SET_INTERSECT], 1, 2, setAsetA, setA);
    m_sigs[OP_FINITE_SET_DIFFERENCE] = alloc(polymorphism::psig, m, m_names[OP_FINITE_SET_DIFFERENCE], 1, 2, setAsetA, setA);
    m_sigs[OP_FINITE_SET_IN]         = alloc(polymorphism::psig, m, m_names[OP_FINITE_SET_IN], 1, 2, AsetA, boolT);
    m_sigs[OP_FINITE_SET_SIZE]       = alloc(polymorphism::psig, m, m_names[OP_FINITE_SET_SIZE], 1, 1, &setA, intT);
    m_sigs[OP_FINITE_SET_SUBSET]     = alloc(polymorphism::psig, m, m_names[OP_FINITE_SET_SUBSET], 1, 2, setAsetA, boolT);
    m_sigs[OP_FINITE_SET_MAP]        = alloc(polymorphism::psig, m, m_names[OP_FINITE_SET_MAP], 2, 2, arrABsetA, setB);
    m_sigs[OP_FINITE_SET_FILTER]     = alloc(polymorphism::psig, m, m_names[OP_FINITE_SET_FILTER], 1, 2, arrABoolsetA, setA);
    m_sigs[OP_FINITE_SET_RANGE]      = alloc(polymorphism::psig, m, m_names[OP_FINITE_SET_RANGE],      0, 2, intintT, setInt);
    m_sigs[OP_FINITE_SET_EXT]        = alloc(polymorphism::psig, m, m_names[OP_FINITE_SET_EXT], 1, 2, setAsetA, A);
    m_sigs[OP_FINITE_SET_MAP_INVERSE] = alloc(polymorphism::psig, m, m_names[OP_FINITE_SET_MAP_INVERSE], 2, 3, arrABBsetA, A);
    m_sigs[OP_FINITE_SET_UNIQUE_SET] = alloc(polymorphism::psig, m, m_names[OP_FINITE_SET_UNIQUE_SET], 1, 2, intintT, setA);
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
        sort_size sz;
        
        // Compute the size of the finite_set sort based on the element sort
        sort_size const& elem_sz = element_sort->get_num_elements();
        if (elem_sz.is_finite() && !elem_sz.is_very_big()) {
            uint64_t elem_size = elem_sz.size();
            // If elem_size > 30, the powerset would be > 2^30, so mark as very_big
            if (elem_size > 30) {
                sz = sort_size::mk_very_big();
            }
            else {
                // Compute 2^elem_size
                sz = sort_size(rational::power_of_two(static_cast<unsigned>(elem_size)));
            }
        }
        else {
            // If element sort is infinite or very_big, the finite_set has the same size
            sz = elem_sz;
        }
        
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
    unsigned np = k == OP_FINITE_SET_UNIQUE_SET ? 1 : 0;
    parameter p(rng.get());
    func_decl_info info(m_family_id, k, np, &p);
    if (k == OP_FINITE_SET_UNION || k == OP_FINITE_SET_INTERSECT) {
        info.set_commutative(true);
        info.set_associative(true);
    }
    return m.mk_func_decl(m_sigs[k]->m_name, arity, domain, rng, info);
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
            range = to_sort(parameters[0].get_ast());
        }        
        return mk_empty(range);
    case OP_FINITE_SET_UNIQUE_SET:
        if (!range) {
            if ((num_parameters != 1 || !parameters[0].is_ast() || !is_sort(parameters[0].get_ast()))) {
                m_manager->raise_exception("set.unique requires one sort parameter");
                return nullptr;
            }
            range = to_sort(parameters[0].get_ast());
        }   
        return mk_finite_set_op(k, arity, domain, range);
    case OP_FINITE_SET_UNION:
    case OP_FINITE_SET_INTERSECT:         
        return mk_finite_set_op(k, 2, domain, range);
    case OP_FINITE_SET_SINGLETON:
    case OP_FINITE_SET_DIFFERENCE:
    case OP_FINITE_SET_IN:
    case OP_FINITE_SET_SIZE:
    case OP_FINITE_SET_SUBSET:
    case OP_FINITE_SET_MAP:
    case OP_FINITE_SET_MAP_INVERSE:
    case OP_FINITE_SET_FILTER:
    case OP_FINITE_SET_RANGE:
    case OP_FINITE_SET_EXT:
        return mk_finite_set_op(k, arity, domain, range);
    default:
        return nullptr;
    }
}

void finite_set_decl_plugin::get_op_names(svector<builtin_name>& op_names, symbol const & logic) {
    for (unsigned i = 0; i < m_names.size(); ++i) 
        if (m_names[i] && i != OP_FINITE_SET_UNIQUE_SET)
            op_names.push_back(builtin_name(std::string(m_names[i]), i));    
}

void finite_set_decl_plugin::get_sort_names(svector<builtin_name>& sort_names, symbol const & logic) {
    sort_names.push_back(builtin_name("FiniteSet", FINITE_SET_SORT));
}

expr * finite_set_decl_plugin::get_some_value(sort * s) {
    if (is_finite_set(s)) {
        // Return empty set for the given sort
        parameter param(s);
        return m_manager->mk_app(m_family_id, OP_FINITE_SET_EMPTY, 1, &param, 0, nullptr);
    }
    return nullptr;
}

bool finite_set_decl_plugin::is_fully_interp(sort * s) const {
    SASSERT(is_finite_set(s));
    sort* element_sort = get_element_sort(s);
    return element_sort && m_manager->is_fully_interp(element_sort);
}

bool finite_set_decl_plugin::is_value(app * e) const {
    // Check if e is a union of either empty sets or singleton sets, 
    // where the singleton member is a value.
    // Use ptr_buffer and expr_fast_mark1 to avoid exponential overhead.
    
    ptr_buffer<expr> todo;
    expr_fast_mark1 visited;
    
    todo.push_back(e);
    
    while (!todo.empty()) {
        expr* current = todo.back();
        todo.pop_back();
        
        // Skip if already visited
        if (visited.is_marked(current))
            continue;
        visited.mark(current);
        
        // Check if current is an app
        if (!is_app(current))
            return false;
            
        app* a = to_app(current);
        
        // Check if it's an empty set
        if (is_app_of(a, m_family_id, OP_FINITE_SET_EMPTY))
            continue;
        
        // Check if it's a singleton with a value element
        if (is_app_of(a, m_family_id, OP_FINITE_SET_SINGLETON)) {
            if (a->get_num_args() != 1)
                return false;
            expr* elem = a->get_arg(0);
            if (!m_manager->is_value(elem))
                return false;
            continue;
        }
        
        // Check if it's a union, intersection, or difference
        bool is_setop = 
            is_app_of(a, m_family_id, OP_FINITE_SET_UNION) 
            || is_app_of(a, m_family_id, OP_FINITE_SET_INTERSECT)
            || is_app_of(a, m_family_id, OP_FINITE_SET_DIFFERENCE);
        if (is_setop) {
            // Add arguments to todo list
            for (auto arg : *a) 
                todo.push_back(arg);            
            continue;
        }

        if (is_app_of(a, m_family_id, OP_FINITE_SET_RANGE)) {
            for (auto arg : *a)
                if (!m_manager->is_value(arg))
                    return false;
            continue;
        }
        
        // If it's none of the above, it's not a value
        return false;
    }
    
    return true;
}

bool finite_set_decl_plugin::is_unique_value(app* e) const {
    // Empty set is a value
    // A singleton of a unique value is tagged as unique
    // ranges are not considered unique even if the bounds are values
    return is_app_of(e, m_family_id, OP_FINITE_SET_EMPTY) ||
           (is_app_of(e, m_family_id, OP_FINITE_SET_SINGLETON) && m_manager->is_unique_value(to_app(e->get_arg(0))));
}

bool finite_set_decl_plugin::are_distinct(app* e1, app* e2) const {
    if (is_unique_value(e1) && is_unique_value(e2))
        return e1 != e2;
    finite_set_recognizers r(get_family_id());   
    if (r.is_empty(e1) && r.is_singleton(e2))
        return true;
    if (r.is_singleton(e1) && r.is_empty(e2))
        return true;
    expr *x = nullptr, *y = nullptr;
    if(r.is_singleton(e1, x) && r.is_singleton(e2, y))
        return m_manager->are_distinct(x, y);
    
    // TODO: could be extended to cases where we can prove the sets are different by containing one element
    // that the other doesn't contain. Such as (union (singleton a) (singleton b)) and (singleton c) where c is different from a, b.
    return false;
}

func_decl *finite_set_util::mk_range_decl() {
    arith_util a(m_manager);
    sort *i = a.mk_int();
    sort *domain[2] = {i, i};
    return m_manager.mk_func_decl(m_fid, OP_FINITE_SET_RANGE, 0, nullptr, 2, domain, nullptr);
}

app* finite_set_util::mk_unique_set(expr* index, expr* cardinality, sort* s) {
    parameter params[1] = { parameter(s) };
    expr *args[2] = {index, cardinality};
    return m_manager.mk_app(m_fid, OP_FINITE_SET_UNIQUE_SET, 1, params, 2, args);
}

