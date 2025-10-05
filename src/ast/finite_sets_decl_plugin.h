/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    finite_sets_decl_plugin.h

Abstract:
    Declaration plugin for finite sets signatures

Sort:
    FiniteSet(S)

Operators:
    set.empty : (FiniteSet S)
    set.singleton : S -> (FiniteSet S)
    set.union : (FiniteSet S) (FiniteSet S) -> (FiniteSet S)
    set.intersect : (FiniteSet S) (FiniteSet S) -> (FiniteSet S)
    set.difference : (FiniteSet S) (FiniteSet S) -> (FiniteSet S)
    set.in : S (FiniteSet S) -> Bool
    set.size : (FiniteSet S) -> Int
    set.subset : (FiniteSet S) (FiniteSet S) -> Bool
    set.map : (S -> T) (FiniteSet S) -> (FiniteSet T)
    set.filter : (S -> Bool) (FiniteSet S) -> (FiniteSet S)
    set.range : Int Int -> (FiniteSet Int)
   
--*/
#pragma once

#include "ast/ast.h"

enum finite_sets_sort_kind {
    FINITE_SET_SORT
};

enum finite_sets_op_kind {
    OP_FINITE_SET_EMPTY,
    OP_FINITE_SET_SINGLETON,
    OP_FINITE_SET_UNION,
    OP_FINITE_SET_INTERSECT,
    OP_FINITE_SET_DIFFERENCE,
    OP_FINITE_SET_IN,
    OP_FINITE_SET_SIZE,
    OP_FINITE_SET_SUBSET,
    OP_FINITE_SET_MAP,
    OP_FINITE_SET_FILTER,
    OP_FINITE_SET_RANGE,
    LAST_FINITE_SET_OP
};

class finite_sets_decl_plugin : public decl_plugin {
    symbol m_empty_sym;
    symbol m_singleton_sym;
    symbol m_union_sym;
    symbol m_intersect_sym;
    symbol m_difference_sym;
    symbol m_in_sym;
    symbol m_size_sym;
    symbol m_subset_sym;
    symbol m_map_sym;
    symbol m_filter_sym;
    symbol m_range_sym;

    func_decl * mk_empty(sort* element_sort);
    func_decl * mk_singleton(unsigned arity, sort * const * domain);
    func_decl * mk_union(unsigned arity, sort * const * domain);
    func_decl * mk_intersect(unsigned arity, sort * const * domain);
    func_decl * mk_difference(unsigned arity, sort * const * domain);
    func_decl * mk_in(unsigned arity, sort * const * domain);
    func_decl * mk_size(unsigned arity, sort * const * domain);
    func_decl * mk_subset(unsigned arity, sort * const * domain);
    func_decl * mk_map(func_decl* f, unsigned arity, sort* const* domain);
    func_decl * mk_filter(func_decl* f, unsigned arity, sort* const* domain);
    func_decl * mk_range(unsigned arity, sort * const * domain);

    bool check_finite_set_arguments(unsigned arity, sort * const * domain);
    sort * get_element_sort(sort* finite_set_sort) const;

public:
    finite_sets_decl_plugin();

    decl_plugin * mk_fresh() override {
        return alloc(finite_sets_decl_plugin);
    }

    //
    // Contract for sort:
    //   parameters[0]     - element sort
    //
    sort * mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters) override;

    //
    // Contract for func_decl:
    //   For OP_FINITE_SET_MAP and OP_FINITE_SET_FILTER:
    //     parameters[0]     - function declaration
    //   For others:
    //     no parameters
    func_decl * mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                             unsigned arity, sort * const * domain, sort * range) override;

    void get_op_names(svector<builtin_name> & op_names, symbol const & logic) override;

    void get_sort_names(svector<builtin_name> & sort_names, symbol const & logic) override;

    expr * get_some_value(sort * s) override;

    bool is_fully_interp(sort * s) const override;

    bool is_value(app * e) const override;

    bool is_unique_value(app* e) const override;
};

class finite_sets_recognizers {
protected:
    family_id m_fid;
public:
    finite_sets_recognizers(family_id fid):m_fid(fid) {}
    family_id get_family_id() const { return m_fid; }
    bool is_finite_set(sort* s) const { return is_sort_of(s, m_fid, FINITE_SET_SORT); }
    bool is_finite_set(expr* n) const { return is_finite_set(n->get_sort()); }
    bool is_empty(expr* n) const { return is_app_of(n, m_fid, OP_FINITE_SET_EMPTY); }
    bool is_singleton(expr* n) const { return is_app_of(n, m_fid, OP_FINITE_SET_SINGLETON); }
    bool is_union(expr* n) const { return is_app_of(n, m_fid, OP_FINITE_SET_UNION); }
    bool is_intersect(expr* n) const { return is_app_of(n, m_fid, OP_FINITE_SET_INTERSECT); }
    bool is_difference(expr* n) const { return is_app_of(n, m_fid, OP_FINITE_SET_DIFFERENCE); }
    bool is_in(expr* n) const { return is_app_of(n, m_fid, OP_FINITE_SET_IN); }
    bool is_size(expr* n) const { return is_app_of(n, m_fid, OP_FINITE_SET_SIZE); }
    bool is_subset(expr* n) const { return is_app_of(n, m_fid, OP_FINITE_SET_SUBSET); }
    bool is_map(expr* n) const { return is_app_of(n, m_fid, OP_FINITE_SET_MAP); }
    bool is_filter(expr* n) const { return is_app_of(n, m_fid, OP_FINITE_SET_FILTER); }
    bool is_range(expr* n) const { return is_app_of(n, m_fid, OP_FINITE_SET_RANGE); }
};

class finite_sets_util : public finite_sets_recognizers {
    ast_manager& m_manager;
public:
    finite_sets_util(ast_manager& m):
        finite_sets_recognizers(m.mk_family_id("finite_sets")), m_manager(m) {}
    
    ast_manager& get_manager() const { return m_manager; }

    app * mk_empty(sort* element_sort) {
        parameter param(element_sort);
        return m_manager.mk_app(m_fid, OP_FINITE_SET_EMPTY, 1, &param, 0, nullptr);
    }

    app * mk_singleton(expr* elem) {
        return m_manager.mk_app(m_fid, OP_FINITE_SET_SINGLETON, elem);
    }

    app * mk_union(expr* s1, expr* s2) {
        return m_manager.mk_app(m_fid, OP_FINITE_SET_UNION, s1, s2);
    }

    app * mk_intersect(expr* s1, expr* s2) {
        return m_manager.mk_app(m_fid, OP_FINITE_SET_INTERSECT, s1, s2);
    }

    app * mk_difference(expr* s1, expr* s2) {
        return m_manager.mk_app(m_fid, OP_FINITE_SET_DIFFERENCE, s1, s2);
    }

    app * mk_in(expr* elem, expr* set) {
        return m_manager.mk_app(m_fid, OP_FINITE_SET_IN, elem, set);
    }

    app * mk_size(expr* set) {
        return m_manager.mk_app(m_fid, OP_FINITE_SET_SIZE, set);
    }

    app * mk_subset(expr* s1, expr* s2) {
        return m_manager.mk_app(m_fid, OP_FINITE_SET_SUBSET, s1, s2);
    }

    app * mk_map(func_decl* f, expr* set) {
        parameter param(f);
        return m_manager.mk_app(m_fid, OP_FINITE_SET_MAP, 1, &param, 1, &set);
    }

    app * mk_filter(func_decl* f, expr* set) {
        parameter param(f);
        return m_manager.mk_app(m_fid, OP_FINITE_SET_FILTER, 1, &param, 1, &set);
    }

    app * mk_range(expr* low, expr* high) {
        return m_manager.mk_app(m_fid, OP_FINITE_SET_RANGE, low, high);
    }
};
