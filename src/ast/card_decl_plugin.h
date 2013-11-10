/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    card_decl_plugin.h

Abstract:

    Cardinality Constraints plugin

Author:

    Nikolaj Bjorner (nbjorner) 2013-05-11

Notes:


  (at-most-k x1 .... x_n) means x1 + ... + x_n <= k
 
hence:

  (not (at-most-k x1 .... x_n)) means x1 + ... + x_n >= k + 1


--*/
#ifndef _CARD_DECL_PLUGIN_H_
#define _CARD_DECL_PLUGIN_H_

#include"ast.h"
 
enum card_op_kind {
    OP_AT_MOST_K,  // at most K Booleans are true.
    OP_PB_LE,      // pseudo-Boolean <= (generalizes at_most_k)
    LAST_CARD_OP
};


class card_decl_plugin : public decl_plugin {
    symbol m_at_most_sym;
    symbol m_pble_sym;
    func_decl * mk_at_most(unsigned arity, unsigned k);
    func_decl * mk_le(unsigned arity, int const* coeffs, int k);
public:
    card_decl_plugin();
    virtual ~card_decl_plugin() {}

    virtual sort * mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters) {
        UNREACHABLE();
        return 0;
    }

    virtual decl_plugin * mk_fresh() {
        return alloc(card_decl_plugin);
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


class card_util {
    ast_manager & m;
    family_id     m_fid;
public:
    card_util(ast_manager& m):m(m), m_fid(m.mk_family_id("card")) {}
    ast_manager & get_manager() const { return m; }
    app * mk_at_most_k(unsigned num_args, expr * const * args, unsigned k);
    app * mk_le(unsigned num_args, int * const* coeffs, expr * const * args, int k);
    bool is_at_most_k(app *a) const;
    bool is_at_most_k(app *a, unsigned& k) const;
    int  get_k(app *a) const;
    bool is_le(app *a) const;
    bool is_le(app* a, int& k) const;
    int  get_le_coeff(app* a, unsigned index); 
};


#endif /* _CARD_DECL_PLUGIN_H_ */

