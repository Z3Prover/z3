/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    pdr_closure.h

Abstract:

    Utility functions for computing closures.

Author:

    Nikolaj Bjorner (nbjorner) 2013-9-1.

Revision History:

--*/

#ifndef PDR_CLOSURE_H_
#define PDR_CLOSURE_H_

#include "ast/arith_decl_plugin.h"

namespace pdr {

    // Arithmetic scaling functor.
    // Variables are replaced using 
    // m_translate. Constants are replaced by
    // multiplication with a variable 'k' (scale factor).
    class scaler {
        ast_manager&          m;
        arith_util            a;
        obj_map<expr, expr*>  m_cache[2];
        expr*                 m_k;
        obj_map<func_decl, expr*>* m_translate;
    public:
        scaler(ast_manager& m): m(m), a(m), m_translate(nullptr) {}
        expr_ref operator()(expr* e, expr* k, obj_map<func_decl, expr*>* translate = nullptr);
        expr_ref undo_k(expr* e, expr* k);
    private:
        expr_ref scale(expr* e, bool is_mul);
    };

    class pred_transformer;

    class closure {
        ast_manager&      m;
        pred_transformer& m_pt;
        arith_util        a;
        bool              m_is_closure;
        expr_ref_vector   m_sigma;
        expr_ref_vector   m_trail;
        vector<obj_map<func_decl, expr*> > m_vars;

        expr_ref relax(unsigned i, expr* fml);
        expr_ref close_conjunction(expr* fml);
        expr_ref close_fml(expr* fml);
        void add_variables(unsigned num_vars, expr_ref_vector& fmls);
    public:
        closure(pred_transformer& pt, bool is_closure);
        expr_ref operator()(expr_ref_vector const& As);
        
    };
}

#endif
