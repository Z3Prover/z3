/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    array_decl_plugin.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-01-09.

Revision History:

--*/
#ifndef ARRAY_DECL_PLUGIN_H_
#define ARRAY_DECL_PLUGIN_H_

#include "ast/ast.h"


inline sort* get_array_range(sort const * s) {
    return to_sort(s->get_parameter(s->get_num_parameters() - 1).get_ast());
}

inline unsigned get_array_arity(sort const * s) {
    return s->get_num_parameters() -1;
}

inline sort* get_array_domain(sort const * s, unsigned idx) {
    return to_sort(s->get_parameter(idx).get_ast());
}

enum array_sort_kind {
    ARRAY_SORT,
    _SET_SORT
};

enum array_op_kind {
    OP_STORE,
    OP_SELECT,
    OP_CONST_ARRAY,
    OP_ARRAY_EXT,
    OP_ARRAY_DEFAULT,
    OP_ARRAY_MAP,
    OP_SET_UNION,
    OP_SET_INTERSECT,
    OP_SET_DIFFERENCE,
    OP_SET_COMPLEMENT,
    OP_SET_SUBSET,
    OP_SET_HAS_SIZE,
    OP_SET_CARD,
    OP_AS_ARRAY, // used for model construction
    LAST_ARRAY_OP
};

class array_decl_plugin : public decl_plugin {
    symbol m_store_sym;
    symbol m_select_sym;
    symbol m_const_sym;
    symbol m_default_sym;
    symbol m_map_sym;
    symbol m_set_union_sym;
    symbol m_set_intersect_sym;
    symbol m_set_difference_sym;
    symbol m_set_complement_sym;
    symbol m_set_subset_sym;
    symbol m_array_ext_sym;
    symbol m_as_array_sym;
    symbol m_set_has_size_sym;
    symbol m_set_card_sym;

    bool check_set_arguments(unsigned arity, sort * const * domain);

    func_decl * mk_const(sort* ty, unsigned arity, sort * const * domain);

    func_decl * mk_map(func_decl* f, unsigned arity, sort* const* domain);

    func_decl * mk_default(unsigned arity, sort* const* domain);

    func_decl * mk_select(unsigned arity, sort * const * domain);

    func_decl * mk_store(unsigned arity, sort * const * domain);

    func_decl * mk_array_ext(unsigned arity, sort * const * domain, unsigned i);

    func_decl * mk_set_union(unsigned arity, sort * const * domain);

    func_decl * mk_set_intersect(unsigned arity, sort * const * domain);

    func_decl * mk_set_difference(unsigned arity, sort * const * domain);

    func_decl * mk_set_complement(unsigned arity, sort * const * domain);

    func_decl * mk_set_subset(unsigned arity, sort * const * domain);

    func_decl * mk_as_array(func_decl * f);

    func_decl* mk_set_has_size(unsigned arity, sort * const* domain);

    func_decl* mk_set_card(unsigned arity, sort * const* domain);

    bool is_array_sort(sort* s) const;
 public:
    array_decl_plugin();
    ~array_decl_plugin() override {}

    decl_plugin * mk_fresh() override {
        return alloc(array_decl_plugin);
    }

    //
    // Contract for sort:
    //   parameters[0]     - 1st dimension
    //   ...
    //   parameters[n-1]   - nth dimension
    //   parameters[n]     - range
    //
    sort * mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters) override;

    //
    // Contract for func_decl:
    //   parameters[0]     - array sort
    // Contract for others:
    //   no parameters
    func_decl * mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                             unsigned arity, sort * const * domain, sort * range) override;

    void get_op_names(svector<builtin_name> & op_names, symbol const & logic) override;

    void get_sort_names(svector<builtin_name> & sort_names, symbol const & logic) override;

    expr * get_some_value(sort * s) override;

    bool is_fully_interp(sort * s) const override;
};

class array_recognizers {
protected:
    family_id m_fid;
public:
    array_recognizers(family_id fid):m_fid(fid) {}
    family_id get_family_id() const { return m_fid; }
    bool is_array(sort* s) const { return is_sort_of(s, m_fid, ARRAY_SORT);}
    bool is_array(expr* n) const { return is_array(get_sort(n)); }
    bool is_select(expr* n) const { return is_app_of(n, m_fid, OP_SELECT); }
    bool is_store(expr* n) const { return is_app_of(n, m_fid, OP_STORE); }
    bool is_const(expr* n) const { return is_app_of(n, m_fid, OP_CONST_ARRAY); }
    bool is_map(expr* n) const { return is_app_of(n, m_fid, OP_ARRAY_MAP); }
    bool is_as_array(expr * n) const { return is_app_of(n, m_fid, OP_AS_ARRAY); }
    bool is_as_array(expr * n, func_decl*& f) const { return is_as_array(n) && (f = get_as_array_func_decl(n), true); }
    bool is_set_has_size(expr* e) const { return is_app_of(e, m_fid, OP_SET_HAS_SIZE); }
    bool is_set_card(expr* e) const { return is_app_of(e, m_fid, OP_SET_CARD); }
    bool is_select(func_decl* f) const { return is_decl_of(f, m_fid, OP_SELECT); }
    bool is_store(func_decl* f) const { return is_decl_of(f, m_fid, OP_STORE); }
    bool is_const(func_decl* f) const { return is_decl_of(f, m_fid, OP_CONST_ARRAY); }
    bool is_map(func_decl* f) const { return is_decl_of(f, m_fid, OP_ARRAY_MAP); }
    bool is_as_array(func_decl* f) const { return is_decl_of(f, m_fid, OP_AS_ARRAY); }
    bool is_set_has_size(func_decl* f) const { return is_decl_of(f, m_fid, OP_SET_HAS_SIZE); }
    bool is_set_card(func_decl* f) const { return is_decl_of(f, m_fid, OP_SET_CARD); }
    bool is_as_array(func_decl* f, func_decl*& g) const { return is_decl_of(f, m_fid, OP_AS_ARRAY) && (g = get_as_array_func_decl(f), true); }
    func_decl * get_as_array_func_decl(expr * n) const;
    func_decl * get_as_array_func_decl(func_decl* f) const;
    func_decl * get_map_func_decl(func_decl* f) const;
    func_decl * get_map_func_decl(expr* e) const { return get_map_func_decl(to_app(e)->get_decl()); }

    bool is_const(expr* e, expr*& v) const;

    bool is_store_ext(expr* e, expr_ref& a, expr_ref_vector& args, expr_ref& value);
};

class array_util : public array_recognizers {
    ast_manager & m_manager;
public:
    array_util(ast_manager& m);
    ast_manager & get_manager() const { return m_manager; }

    bool is_as_array_tree(expr * n);

    app * mk_store(unsigned num_args, expr * const * args) {
        return m_manager.mk_app(m_fid, OP_STORE, 0, nullptr, num_args, args);
    }

    app * mk_select(unsigned num_args, expr * const * args) {
        return m_manager.mk_app(m_fid, OP_SELECT, 0, nullptr, num_args, args);
    }

    app * mk_select(ptr_vector<expr> const& args) {
        return mk_select(args.size(), args.c_ptr());
    }

    app * mk_select(expr_ref_vector const& args) {
        return mk_select(args.size(), args.c_ptr());
    }

    app * mk_map(func_decl * f, unsigned num_args, expr * const * args) {
        parameter p(f);
        return m_manager.mk_app(m_fid, OP_ARRAY_MAP, 1, &p, num_args, args);
    }

    expr * mk_map_assoc(func_decl * f, unsigned num_args, expr * const * args) {
        expr* r = args[0];
        for (unsigned i = 1; i < num_args; ++i) {
            expr* es[2] = { r, args[i] };
            r = mk_map(f, 2, es);
        }
        return r;
    }

    app * mk_const_array(sort * s, expr * v) {
        parameter param(s);
        return m_manager.mk_app(m_fid, OP_CONST_ARRAY, 1, &param, 1, &v);
    }
    app * mk_empty_set(sort * s) {
        return mk_const_array(s, m_manager.mk_false());
    }
    app * mk_full_set(sort * s) {
        return mk_const_array(s, m_manager.mk_true());
    }

    app * mk_setminus(expr* s1, expr* s2) {
        return m_manager.mk_app(m_fid, OP_SET_DIFFERENCE, s1, s2);
    }

    app * mk_intersection(expr* s1, expr* s2) {
        return m_manager.mk_app(m_fid, OP_SET_INTERSECT, s1, s2);
    }

    app * mk_union(expr* s1, expr* s2) {
        return m_manager.mk_app(m_fid, OP_SET_UNION, s1, s2);
    }

    app* mk_has_size(expr* set, expr* n) {
        return m_manager.mk_app(m_fid, OP_SET_HAS_SIZE, set, n);
    }

    app* mk_card(expr* set) {
        return m_manager.mk_app(m_fid, OP_SET_CARD, set);
    }

    func_decl * mk_array_ext(sort* domain, unsigned i);

    sort * mk_array_sort(sort* dom, sort* range) { return mk_array_sort(1, &dom, range); }

    sort * mk_array_sort(unsigned arity, sort* const* domain, sort* range);

    app * mk_as_array(func_decl * f) {
        parameter param(f);
        return m_manager.mk_app(m_fid, OP_AS_ARRAY, 1, &param, 0, nullptr, nullptr);
    }
};


#endif /* ARRAY_DECL_PLUGIN_H_ */

