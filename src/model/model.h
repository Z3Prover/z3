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
#include "model/model_evaluator.h"
#include "util/ref.h"
#include "ast/ast_translation.h"

class model;
typedef ref<model> model_ref;

class model : public model_core {
protected:
    typedef obj_map<sort, ptr_vector<expr>*> sort2universe;
    typedef obj_hashtable<func_decl> func_decl_set;

    ptr_vector<sort>              m_usorts;
    sort2universe                 m_usort2universe;
    model_evaluator               m_mev;
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
    ~model() override;

    void copy_func_interps(model const & source);
    void copy_const_interps(model const & source);
    void copy_usort_interps(model const & source);

    model * copy() const;

    bool eval_expr(expr * e, expr_ref & result, bool model_completion = false);

    expr * get_some_value(sort * s) override;
    ptr_vector<expr> const & get_universe(sort * s) const override;
    unsigned get_num_uninterpreted_sorts() const override;
    sort * get_uninterpreted_sort(unsigned idx) const override;
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

    void set_model_completion(bool f) { m_mev.set_model_completion(f); }
    void updt_params(params_ref const & p) { m_mev.updt_params(p); }

    /**
     * evaluation using the model evaluator. Caches results.
     */
    expr_ref operator()(expr* t);
    expr_ref_vector operator()(expr_ref_vector const& ts);
    bool is_true(expr* t);
    bool is_false(expr* t);
    bool is_true(expr_ref_vector const& ts);
    void reset_eval_cache();

    class scoped_model_completion {
        bool   m_old_completion;
        model& m_model;
    public:
        scoped_model_completion(model& m, bool c):
            m_old_completion(m.m_mev.get_model_completion()), m_model(m) {
            m.set_model_completion(c);
        }
        scoped_model_completion(model_ref& m, bool c):
            m_old_completion(m->m_mev.get_model_completion()), m_model(*m.get()) {
            m->set_model_completion(c);
        }
        ~scoped_model_completion() {
            m_model.set_model_completion(m_old_completion);
        }
    };
};


#endif /* MODEL_H_ */
