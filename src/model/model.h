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

#include "model/model_core.h"
#include "util/ref.h"
#include "ast/ast_translation.h"

class model : public model_core {
protected:
    typedef obj_map<sort, ptr_vector<expr>*> sort2universe;
    typedef obj_hashtable<func_decl> func_decl_set;

    ptr_vector<sort>              m_usorts;
    sort2universe                 m_usort2universe;
    bool                          m_cleaned;
    struct value_proc;

    void collect_deps(obj_map<func_decl, func_decl_set*>& deps);
    func_decl_set* collect_deps(expr * e);
    func_decl_set* collect_deps(func_interp* fi);
    struct deps_collector;
    
    struct top_sort;
    void topological_sort(top_sort& st);
    void traverse(top_sort& st, func_decl* f);
    bool is_singleton_partition(top_sort& st, func_decl* f) const;
    
    void cleanup_interp(top_sort&_st, func_decl * f);
    expr_ref cleanup_expr(top_sort& st, expr* e, unsigned current_partition);
    void remove_decls(ptr_vector<func_decl> & decls, func_decl_set const & s);

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

    expr_ref get_inlined_const_interp(func_decl* f);

    //
    // Primitives for building models
    //
    void register_usort(sort * s, unsigned usize, expr * const * universe);

    // Model translation
    //
    model * translate(ast_translation & translator) const;

    void cleanup();
};

typedef ref<model> model_ref;

#endif /* MODEL_H_ */

