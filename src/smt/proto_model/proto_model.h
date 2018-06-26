/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    proto_model.h

Abstract:

    This is the old model object.
    smt::context used it during model construction and for
    reporting the model for external consumers. 
    The whole value_factory "business" was due to model construction
    and unnecessary for external consumers.
    Future solvers will not use value_factory objects for 
    helping during model construction. 
    
    After smt::context finishes building the model, it is converted
    into a new (light) model object.

Author:

    Leonardo de Moura (leonardo) 2007-03-08.

Revision History:

--*/
#ifndef PROTO_MODEL_H_
#define PROTO_MODEL_H_

#include "model/model_core.h"
#include "model/model_evaluator.h"
#include "smt/proto_model/value_factory.h"
#include "util/plugin_manager.h"
#include "ast/arith_decl_plugin.h"
#include "ast/func_decl_dependencies.h"
#include "model/model.h"
#include "util/params.h"
#include "ast/rewriter/th_rewriter.h"


class proto_model : public model_core {
    plugin_manager<value_factory> m_factories;
    user_sort_factory *           m_user_sort_factory;
    func_decl_set                 m_aux_decls;
    ptr_vector<expr>              m_tmp;
    model_evaluator               m_eval;
    th_rewriter                   m_rewrite;

    bool                          m_model_partial;

    expr * mk_some_interp_for(func_decl * d);

    // Invariant: m_decls subset m_func_decls union m_const_decls union union m_value_decls
    // Invariant: m_func_decls  subset m_decls
    // Invariant: m_const_decls subset m_decls
    
    void remove_aux_decls_not_in_set(ptr_vector<func_decl> & decls, func_decl_set const & s);
    void cleanup_func_interp(func_interp * fi, func_decl_set & found_aux_fs);


public:
    proto_model(ast_manager & m, params_ref const & p = params_ref());
    ~proto_model() override {}

    void register_factory(value_factory * f) { m_factories.register_plugin(f); }

    bool eval(expr * e, expr_ref & result, bool model_completion = false);

    
    value_factory * get_factory(family_id fid);

    expr * get_some_value(sort * s) override;

    bool get_some_values(sort * s, expr_ref & v1, expr_ref & v2);

    expr * get_fresh_value(sort * s);

    void register_value(expr * n);

    //
    // Primitives for building models
    //
    void register_aux_decl(func_decl * f, func_interp * fi);
    void register_aux_decl(func_decl * f);
    void reregister_decl(func_decl * f, func_interp * new_fi, func_decl * f_aux);
    void compress();
    void cleanup();

    //
    // Primitives for building finite interpretations for uninterpreted sorts,
    // and retrieving the known universe.
    //
    void freeze_universe(sort * s);
    bool is_finite(sort * s) const;
    obj_hashtable<expr> const & get_known_universe(sort * s) const;
    ptr_vector<expr> const & get_universe(sort * s) const override;
    unsigned get_num_uninterpreted_sorts() const override;
    sort * get_uninterpreted_sort(unsigned idx) const override;

    //
    // Complete partial function interps
    //
    void complete_partial_func(func_decl * f, bool use_fresh);
    void complete_partial_funcs(bool use_fresh);

    //
    // Create final model object. 
    // proto_model is corrupted after that.
    model * mk_model();
};

typedef ref<proto_model> proto_model_ref;

#endif /* PROTO_MODEL_H_ */

