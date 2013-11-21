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
#ifndef _PB_DECL_PLUGIN_H_
#define _PB_DECL_PLUGIN_H_

#include"ast.h"
 
enum pb_op_kind {
    OP_AT_MOST_K,  // at most K Booleans are true.
    OP_AT_LEAST_K, // at least K Booleans are true.
    OP_PB_LE,      // pseudo-Boolean <= (generalizes at_most_k)
    OP_PB_GE,      // pseudo-Boolean >= 
    LAST_PB_OP
};


class pb_decl_plugin : public decl_plugin {
    symbol m_at_most_sym;
    symbol m_at_least_sym;
    symbol m_pble_sym;
    symbol m_pbge_sym;
    func_decl * mk_at_most(unsigned arity, unsigned k);
    func_decl * mk_at_least(unsigned arity, unsigned k);
    func_decl * mk_le(unsigned arity, rational const* coeffs, int k);
    func_decl * mk_ge(unsigned arity, rational const* coeffs, int k);
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
    bool is_at_most_k(app *a) const;
    bool is_at_most_k(app *a, rational& k) const;
    bool is_at_least_k(app *a) const;
    bool is_at_least_k(app *a, rational& k) const;
    rational get_k(app *a) const;
    bool is_le(app *a) const;
    bool is_le(app* a, rational& k) const;
    bool is_ge(app* a) const;
    bool is_ge(app* a, rational& k) const;
    rational get_coeff(app* a, unsigned index); 
};




#endif /* _PB_DECL_PLUGIN_H_ */

