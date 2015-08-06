/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    pb_decl_plugin.h

Abstract:

    Pseudo-Boolean and Cardinality Constraints plugin

Author:

    Nikolaj Bjorner (nbjorner) 2013-05-11

Notes:


  (at-most-k x1 .... x_n) means x1 + ... + x_n <= k
 
hence:

  (not (at-most-k x1 .... x_n)) means x1 + ... + x_n >= k + 1


--*/
#ifndef PB_DECL_PLUGIN_H_
#define PB_DECL_PLUGIN_H_

#include"ast.h"
 
enum pb_op_kind {
    OP_AT_MOST_K,  // at most K Booleans are true.
    OP_AT_LEAST_K, // at least K Booleans are true.
    OP_PB_LE,      // pseudo-Boolean <= (generalizes at_most_k)
    OP_PB_GE,      // pseudo-Boolean >= 
    OP_PB_EQ,      // equality
    OP_PB_AUX_BOOL, // auxiliary internal Boolean variable.
    LAST_PB_OP
};


class pb_decl_plugin : public decl_plugin {
    symbol m_at_most_sym;
    symbol m_at_least_sym;
    symbol m_pble_sym;
    symbol m_pbge_sym;
    symbol m_pbeq_sym;
    func_decl * mk_at_most(unsigned arity, unsigned k);
    func_decl * mk_at_least(unsigned arity, unsigned k);
    func_decl * mk_le(unsigned arity, rational const* coeffs, int k);
    func_decl * mk_ge(unsigned arity, rational const* coeffs, int k);
    func_decl * mk_eq(unsigned arity, rational const* coeffs, int k);
public:
    pb_decl_plugin();
    virtual ~pb_decl_plugin() {}

    virtual sort * mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters) {
        UNREACHABLE();
        return 0;
    }

    virtual decl_plugin * mk_fresh() {
        return alloc(pb_decl_plugin);
    }
    
    //
    // Contract for func_decl:
    //   parameters[0] - integer (at most k elements)
    //      all sorts are Booleans
    //    parameters[1] .. parameters[arity] - coefficients
    virtual func_decl * mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters, 
                                     unsigned arity, sort * const * domain, sort * range);
    virtual void get_op_names(svector<builtin_name> & op_names, symbol const & logic);

};


class pb_util {
    ast_manager & m;
    family_id     m_fid;
public:
    pb_util(ast_manager& m):m(m), m_fid(m.mk_family_id("pb")) {}
    ast_manager & get_manager() const { return m; }
    family_id get_family_id() const { return m_fid; }
    app * mk_at_most_k(unsigned num_args, expr * const * args, unsigned k);
    app * mk_at_least_k(unsigned num_args, expr * const * args, unsigned k);
    app * mk_le(unsigned num_args, rational const * coeffs, expr * const * args, rational const& k);
    app * mk_ge(unsigned num_args, rational const * coeffs, expr * const * args, rational const& k);
    app * mk_eq(unsigned num_args, rational const * coeffs, expr * const * args, rational const& k);
    app * mk_lt(unsigned num_args, rational const * coeffs, expr * const * args, rational const& k);
    bool is_at_most_k(func_decl *a) const;
    bool is_at_most_k(expr *a) const { return is_app(a) && is_at_most_k(to_app(a)->get_decl()); }
    bool is_at_most_k(expr *a, rational& k) const;
    bool is_at_least_k(func_decl *a) const;
    bool is_at_least_k(expr *a) const { return is_app(a) && is_at_least_k(to_app(a)->get_decl()); }
    bool is_at_least_k(expr *a, rational& k) const;
    rational get_k(func_decl *a) const;
    rational get_k(expr *a) const { return get_k(to_app(a)->get_decl()); }
    bool is_le(func_decl *a) const;
    bool is_le(expr *a) const { return is_app(a) && is_le(to_app(a)->get_decl()); }
    bool is_le(expr* a, rational& k) const;
    bool is_ge(func_decl* a) const;
    bool is_ge(expr* a) const { return is_app(a) && is_ge(to_app(a)->get_decl()); }
    bool is_ge(expr* a, rational& k) const;
    bool is_aux_bool(expr* e) const { return is_app_of(e, m_fid, OP_PB_AUX_BOOL); }
    rational get_coeff(expr* a, unsigned index) const { return get_coeff(to_app(a)->get_decl(), index); }
    rational get_coeff(func_decl* a, unsigned index) const; 
    bool has_unit_coefficients(func_decl* f) const;
    bool has_unit_coefficients(expr* f) const { return is_app(f) && has_unit_coefficients(to_app(f)->get_decl()); }


    bool is_eq(func_decl* f) const;
    bool is_eq(expr* e) const { return is_app(e) && is_eq(to_app(e)->get_decl()); }
    bool is_eq(expr* e, rational& k) const;

    app* mk_fresh_bool();


private:
    rational to_rational(parameter const& p) const;
};




#endif /* PB_DECL_PLUGIN_H_ */

