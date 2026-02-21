/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    finite_set_decl_plugin.h

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
    set.diff : (FiniteSet S) (FiniteSet S) -> S
   
--*/
#pragma once

#include "ast/ast.h"
#include "ast/polymorphism_util.h"

enum finite_set_sort_kind {
    FINITE_SET_SORT
};

enum finite_set_op_kind {
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
    OP_FINITE_SET_EXT,
    OP_FINITE_SET_MAP_INVERSE,
    OP_FINITE_SET_UNIQUE_SET,
    LAST_FINITE_SET_OP
};

class finite_set_decl_plugin : public decl_plugin {
    ptr_vector<polymorphism::psig>   m_sigs;
    svector<char const*>             m_names;
    bool                             m_init{false};

    void init();
    func_decl * mk_empty(sort* set_sort);
    func_decl * mk_finite_set_op(decl_kind k, unsigned arity, sort * const * domain, sort* range);
    sort * get_element_sort(sort* finite_set_sort) const;
    bool is_finite_set(sort* s) const;

public:
    finite_set_decl_plugin();
    ~finite_set_decl_plugin() override;

    decl_plugin * mk_fresh() override {
        return alloc(finite_set_decl_plugin);
    }
    
    void finalize() override {
        for (polymorphism::psig* s : m_sigs) 
            dealloc(s);
        m_sigs.reset();
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

    bool are_distinct(app *e1, app *e2) const override;

};

class finite_set_recognizers {
protected:
    family_id m_fid;
public:
    finite_set_recognizers(family_id fid):m_fid(fid) {}
    family_id get_family_id() const { return m_fid; }
    bool is_finite_set(sort* s) const { return is_sort_of(s, m_fid, FINITE_SET_SORT); }
    bool is_finite_set(sort* s, sort*& elem_sort) const {
        if (is_finite_set(s)) {
            elem_sort = to_sort(s->get_parameter(0).get_ast());
            return true;
        }
        return false;
    }
    bool is_finite_set(expr const* n) const { return is_finite_set(n->get_sort()); }
    bool is_empty(expr const* n) const { return is_app_of(n, m_fid, OP_FINITE_SET_EMPTY); }
    bool is_singleton(expr const* n) const { return is_app_of(n, m_fid, OP_FINITE_SET_SINGLETON); }
    bool is_union(expr const* n) const { return is_app_of(n, m_fid, OP_FINITE_SET_UNION); }
    bool is_intersect(expr const* n) const { return is_app_of(n, m_fid, OP_FINITE_SET_INTERSECT); }
    bool is_difference(expr const* n) const { return is_app_of(n, m_fid, OP_FINITE_SET_DIFFERENCE); }
    bool is_in(expr const* n) const { return is_app_of(n, m_fid, OP_FINITE_SET_IN); }
    bool is_size(expr const* n) const { return is_app_of(n, m_fid, OP_FINITE_SET_SIZE); }
    bool is_subset(expr const* n) const { return is_app_of(n, m_fid, OP_FINITE_SET_SUBSET); }
    bool is_map(expr const* n) const { return is_app_of(n, m_fid, OP_FINITE_SET_MAP); }
    bool is_filter(expr const* n) const { return is_app_of(n, m_fid, OP_FINITE_SET_FILTER); }
    bool is_range(expr const* n) const { return is_app_of(n, m_fid, OP_FINITE_SET_RANGE); }
    bool is_unique_set(expr const *n) const { return is_app_of(n, m_fid, OP_FINITE_SET_UNIQUE_SET); } 

    MATCH_UNARY(is_singleton);
    MATCH_UNARY(is_size);
    MATCH_BINARY(is_union);
    MATCH_BINARY(is_intersect);
    MATCH_BINARY(is_difference);
    MATCH_BINARY(is_in);
    MATCH_BINARY(is_subset);
    MATCH_BINARY(is_map);
    MATCH_BINARY(is_filter);
    MATCH_BINARY(is_range);
    MATCH_BINARY(is_unique_set);
};

class finite_set_util : public finite_set_recognizers {
    ast_manager& m_manager;
public:
    finite_set_util(ast_manager& m):
        finite_set_recognizers(m.mk_family_id("finite_set")), m_manager(m) {}
    
    ast_manager& get_manager() const { return m_manager; }

    sort *mk_finite_set_sort(sort *elem_sort) {
        parameter param(elem_sort);
        return m_manager.mk_sort(m_fid, FINITE_SET_SORT, 1, &param);
    }

    app * mk_empty(sort* set_sort) {
        parameter param(set_sort);
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

    app *mk_ext(expr *s1, expr *s2) {
        return m_manager.mk_app(m_fid, OP_FINITE_SET_EXT, s1, s2);
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

    app * mk_map(expr* arr, expr* set) {
        return m_manager.mk_app(m_fid, OP_FINITE_SET_MAP, arr, set);
    }

    app *mk_map_inverse(expr *f, expr *x, expr *b) {
        return m_manager.mk_app(m_fid, OP_FINITE_SET_MAP_INVERSE, f, x, b);
    }

    app * mk_filter(expr* arr, expr* set) {
        return m_manager.mk_app(m_fid, OP_FINITE_SET_FILTER, arr, set);
    }

    func_decl *mk_range_decl();

    app *mk_range(expr *low, expr *high) {
        return m_manager.mk_app(m_fid, OP_FINITE_SET_RANGE, low, high);
    }

    app *mk_unique_set(expr *s1, expr *s2, sort *s);
};
