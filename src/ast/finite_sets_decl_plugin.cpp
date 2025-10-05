/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    finite_sets_decl_plugin.cpp

Abstract:

    Declaration plugin for finite sets

Author:

    GitHub Copilot Agent 2025

Revision History:

--*/
#include<sstream>
#include "ast/finite_sets_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "util/warning.h"

finite_sets_decl_plugin::finite_sets_decl_plugin():
    m_empty_sym("set.empty"),
    m_union_sym("set.union"),
    m_intersect_sym("set.intersect"),
    m_difference_sym("set.difference"),
    m_in_sym("set.in"),
    m_size_sym("set.size"),
    m_subset_sym("set.subset"),
    m_map_sym("set.map"),
    m_filter_sym("set.filter"),
    m_range_sym("set.range") {
}

sort * finite_sets_decl_plugin::mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters) {
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

sort * finite_sets_decl_plugin::get_element_sort(sort* finite_set_sort) const {
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

bool finite_sets_decl_plugin::check_finite_set_arguments(unsigned arity, sort * const * domain) {
    if (arity == 0) {
        return true;
    }
    
    sort* first_sort = domain[0];
    if (first_sort->get_family_id() != m_family_id || 
        first_sort->get_decl_kind() != FINITE_SET_SORT) {
        m_manager->raise_exception("argument is not of FiniteSet sort");
        return false;
    }
    
    for (unsigned i = 1; i < arity; ++i) {
        if (domain[i] != first_sort) {
            std::ostringstream buffer;
            buffer << "arguments " << 1 << " and " << (i+1) << " have different sorts";
            m_manager->raise_exception(buffer.str());
            return false;
        }
    }
    return true;
}

func_decl * finite_sets_decl_plugin::mk_empty(sort* element_sort) {
    parameter param(element_sort);
    sort * finite_set_sort = m_manager->mk_sort(m_family_id, FINITE_SET_SORT, 1, &param);
    sort * const * no_domain = nullptr;
    return m_manager->mk_func_decl(m_empty_sym, 0u, no_domain, finite_set_sort,
                                   func_decl_info(m_family_id, OP_FINITE_SET_EMPTY, 1, &param));
}

func_decl * finite_sets_decl_plugin::mk_union(unsigned arity, sort * const * domain) {
    if (arity != 2) {
        m_manager->raise_exception("set.union takes exactly two arguments");
        return nullptr;
    }
    if (!check_finite_set_arguments(arity, domain)) {
        return nullptr;
    }
    return m_manager->mk_func_decl(m_union_sym, arity, domain, domain[0],
                                   func_decl_info(m_family_id, OP_FINITE_SET_UNION));
}

func_decl * finite_sets_decl_plugin::mk_intersect(unsigned arity, sort * const * domain) {
    if (arity != 2) {
        m_manager->raise_exception("set.intersect takes exactly two arguments");
        return nullptr;
    }
    if (!check_finite_set_arguments(arity, domain)) {
        return nullptr;
    }
    return m_manager->mk_func_decl(m_intersect_sym, arity, domain, domain[0],
                                   func_decl_info(m_family_id, OP_FINITE_SET_INTERSECT));
}

func_decl * finite_sets_decl_plugin::mk_difference(unsigned arity, sort * const * domain) {
    if (arity != 2) {
        m_manager->raise_exception("set.difference takes exactly two arguments");
        return nullptr;
    }
    if (!check_finite_set_arguments(arity, domain)) {
        return nullptr;
    }
    return m_manager->mk_func_decl(m_difference_sym, arity, domain, domain[0],
                                   func_decl_info(m_family_id, OP_FINITE_SET_DIFFERENCE));
}

func_decl * finite_sets_decl_plugin::mk_in(unsigned arity, sort * const * domain) {
    if (arity != 2) {
        m_manager->raise_exception("set.in takes exactly two arguments");
        return nullptr;
    }
    if (domain[1]->get_family_id() != m_family_id ||
        domain[1]->get_decl_kind() != FINITE_SET_SORT) {
        m_manager->raise_exception("second argument of set.in must be a FiniteSet");
        return nullptr;
    }
    
    sort* element_sort = get_element_sort(domain[1]);
    if (!element_sort) {
        m_manager->raise_exception("invalid FiniteSet sort");
        return nullptr;
    }
    
    if (domain[0] != element_sort) {
        m_manager->raise_exception("element type does not match set element type");
        return nullptr;
    }
    
    sort* bool_sort = m_manager->mk_bool_sort();
    return m_manager->mk_func_decl(m_in_sym, arity, domain, bool_sort,
                                   func_decl_info(m_family_id, OP_FINITE_SET_IN));
}

func_decl * finite_sets_decl_plugin::mk_size(unsigned arity, sort * const * domain) {
    if (arity != 1) {
        m_manager->raise_exception("set.size takes exactly one argument");
        return nullptr;
    }
    if (!check_finite_set_arguments(arity, domain)) {
        return nullptr;
    }
    
    arith_util arith(*m_manager);
    sort * int_sort = arith.mk_int();
    return m_manager->mk_func_decl(m_size_sym, arity, domain, int_sort,
                                   func_decl_info(m_family_id, OP_FINITE_SET_SIZE));
}

func_decl * finite_sets_decl_plugin::mk_subset(unsigned arity, sort * const * domain) {
    if (arity != 2) {
        m_manager->raise_exception("set.subset takes exactly two arguments");
        return nullptr;
    }
    if (!check_finite_set_arguments(arity, domain)) {
        return nullptr;
    }
    
    sort* bool_sort = m_manager->mk_bool_sort();
    return m_manager->mk_func_decl(m_subset_sym, arity, domain, bool_sort,
                                   func_decl_info(m_family_id, OP_FINITE_SET_SUBSET));
}

func_decl * finite_sets_decl_plugin::mk_map(func_decl* f, unsigned arity, sort* const* domain) {
    if (arity != 1) {
        m_manager->raise_exception("set.map takes exactly one set argument");
        return nullptr;
    }
    if (!check_finite_set_arguments(arity, domain)) {
        return nullptr;
    }
    
    // Get the element sort of the input set
    sort* input_element_sort = get_element_sort(domain[0]);
    if (!input_element_sort) {
        m_manager->raise_exception("invalid FiniteSet sort");
        return nullptr;
    }
    
    // Check that the function has correct signature
    if (f->get_arity() != 1) {
        m_manager->raise_exception("set.map function must take exactly one argument");
        return nullptr;
    }
    if (f->get_domain(0) != input_element_sort) {
        m_manager->raise_exception("set.map function domain must match set element type");
        return nullptr;
    }
    
    // Create output set sort with the function's range as element type
    sort* output_element_sort = f->get_range();
    parameter param(output_element_sort);
    sort* output_set_sort = m_manager->mk_sort(m_family_id, FINITE_SET_SORT, 1, &param);
    
    parameter func_param(f);
    return m_manager->mk_func_decl(m_map_sym, arity, domain, output_set_sort,
                                   func_decl_info(m_family_id, OP_FINITE_SET_MAP, 1, &func_param));
}

func_decl * finite_sets_decl_plugin::mk_filter(func_decl* f, unsigned arity, sort* const* domain) {
    if (arity != 1) {
        m_manager->raise_exception("set.filter takes exactly one set argument");
        return nullptr;
    }
    if (!check_finite_set_arguments(arity, domain)) {
        return nullptr;
    }
    
    // Get the element sort of the set
    sort* element_sort = get_element_sort(domain[0]);
    if (!element_sort) {
        m_manager->raise_exception("invalid FiniteSet sort");
        return nullptr;
    }
    
    // Check that the function has correct signature (S -> Bool)
    if (f->get_arity() != 1) {
        m_manager->raise_exception("set.filter function must take exactly one argument");
        return nullptr;
    }
    if (f->get_domain(0) != element_sort) {
        m_manager->raise_exception("set.filter function domain must match set element type");
        return nullptr;
    }
    if (!m_manager->is_bool(f->get_range())) {
        m_manager->raise_exception("set.filter function must return Bool");
        return nullptr;
    }
    
    parameter func_param(f);
    return m_manager->mk_func_decl(m_filter_sym, arity, domain, domain[0],
                                   func_decl_info(m_family_id, OP_FINITE_SET_FILTER, 1, &func_param));
}

func_decl * finite_sets_decl_plugin::mk_range(unsigned arity, sort * const * domain) {
    if (arity != 2) {
        m_manager->raise_exception("set.range takes exactly two arguments");
        return nullptr;
    }
    
    arith_util arith(*m_manager);
    sort * int_sort = arith.mk_int();
    
    if (domain[0] != int_sort || domain[1] != int_sort) {
        m_manager->raise_exception("set.range arguments must be Int");
        return nullptr;
    }
    
    parameter param(int_sort);
    sort* output_set_sort = m_manager->mk_sort(m_family_id, FINITE_SET_SORT, 1, &param);
    
    return m_manager->mk_func_decl(m_range_sym, arity, domain, output_set_sort,
                                   func_decl_info(m_family_id, OP_FINITE_SET_RANGE));
}

func_decl * finite_sets_decl_plugin::mk_func_decl(decl_kind k, unsigned num_parameters, 
                                                   parameter const * parameters,
                                                   unsigned arity, sort * const * domain, 
                                                   sort * range) {
    switch (k) {
    case OP_FINITE_SET_EMPTY:
        if (num_parameters != 1 || !parameters[0].is_ast() || !is_sort(parameters[0].get_ast())) {
            m_manager->raise_exception("set.empty requires one sort parameter");
            return nullptr;
        }
        return mk_empty(to_sort(parameters[0].get_ast()));
    case OP_FINITE_SET_UNION:
        return mk_union(arity, domain);
    case OP_FINITE_SET_INTERSECT:
        return mk_intersect(arity, domain);
    case OP_FINITE_SET_DIFFERENCE:
        return mk_difference(arity, domain);
    case OP_FINITE_SET_IN:
        return mk_in(arity, domain);
    case OP_FINITE_SET_SIZE:
        return mk_size(arity, domain);
    case OP_FINITE_SET_SUBSET:
        return mk_subset(arity, domain);
    case OP_FINITE_SET_MAP:
        if (num_parameters != 1 || !parameters[0].is_ast() || !is_func_decl(parameters[0].get_ast())) {
            m_manager->raise_exception("set.map requires one function parameter");
            return nullptr;
        }
        return mk_map(to_func_decl(parameters[0].get_ast()), arity, domain);
    case OP_FINITE_SET_FILTER:
        if (num_parameters != 1 || !parameters[0].is_ast() || !is_func_decl(parameters[0].get_ast())) {
            m_manager->raise_exception("set.filter requires one function parameter");
            return nullptr;
        }
        return mk_filter(to_func_decl(parameters[0].get_ast()), arity, domain);
    case OP_FINITE_SET_RANGE:
        return mk_range(arity, domain);
    default:
        return nullptr;
    }
}

void finite_sets_decl_plugin::get_op_names(svector<builtin_name>& op_names, symbol const & logic) {
    op_names.push_back(builtin_name("set.empty", OP_FINITE_SET_EMPTY));
    op_names.push_back(builtin_name("set.union", OP_FINITE_SET_UNION));
    op_names.push_back(builtin_name("set.intersect", OP_FINITE_SET_INTERSECT));
    op_names.push_back(builtin_name("set.difference", OP_FINITE_SET_DIFFERENCE));
    op_names.push_back(builtin_name("set.in", OP_FINITE_SET_IN));
    op_names.push_back(builtin_name("set.size", OP_FINITE_SET_SIZE));
    op_names.push_back(builtin_name("set.subset", OP_FINITE_SET_SUBSET));
    op_names.push_back(builtin_name("set.map", OP_FINITE_SET_MAP));
    op_names.push_back(builtin_name("set.filter", OP_FINITE_SET_FILTER));
    op_names.push_back(builtin_name("set.range", OP_FINITE_SET_RANGE));
}

void finite_sets_decl_plugin::get_sort_names(svector<builtin_name>& sort_names, symbol const & logic) {
    sort_names.push_back(builtin_name("FiniteSet", FINITE_SET_SORT));
}

expr * finite_sets_decl_plugin::get_some_value(sort * s) {
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

bool finite_sets_decl_plugin::is_fully_interp(sort * s) const {
    return s->get_family_id() == m_family_id && s->get_decl_kind() == FINITE_SET_SORT;
}

bool finite_sets_decl_plugin::is_value(app * e) const {
    // Empty set is a value
    return is_app_of(e, m_family_id, OP_FINITE_SET_EMPTY);
}

bool finite_sets_decl_plugin::is_unique_value(app* e) const {
    // Empty set is a unique value for its sort
    return is_value(e);
}
