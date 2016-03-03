/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    model.h

Abstract:

    Model for satisfiable formulas

Author:

    Leonardo de Moura (leonardo) 2011-04-30.

Revision History:

--*/
#ifndef MODEL_H_
#define MODEL_H_

#include"model_core.h"
#include"ref.h"
#include"ast_translation.h"

class model : public model_core {
protected:
    typedef obj_map<sort, ptr_vector<expr>*> sort2universe;
    
    ptr_vector<sort>              m_usorts;
    sort2universe                 m_usort2universe;
    struct value_proc;

public:
    model(ast_manager & m);
    virtual ~model(); 

    void copy_func_interps(model const & source);
    void copy_const_interps(model const & source);
    void copy_usort_interps(model const & source);

    model * copy() const;
    
    bool eval(func_decl * f, expr_ref & r) const { return model_core::eval(f, r); }
    bool eval(expr * e, expr_ref & result, bool model_completion = false);
    
    virtual expr * get_some_value(sort * s);
    virtual ptr_vector<expr> const & get_universe(sort * s) const;
    virtual unsigned get_num_uninterpreted_sorts() const;
    virtual sort * get_uninterpreted_sort(unsigned idx) const;
    bool has_uninterpreted_sort(sort * s) const; 

    //
    // Primitives for building models
    //
    void register_usort(sort * s, unsigned usize, expr * const * universe);

    // Model translation
    //
    model * translate(ast_translation & translator) const;
};

typedef ref<model> model_ref;

#endif /* MODEL_H_ */

