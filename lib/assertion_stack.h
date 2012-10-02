/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    assertion_stack.h

Abstract:

    It should be viewed as the "goal" object for incremental solvers.
    The main difference is the support of push/pop operations.  Like a
    goal, an assertion_stack contains expressions, their proofs (if
    proof generation is enabled), and dependencies (if unsat core
    generation is enabled).

    The assertions on the stack are grouped by scope levels. Scoped
    levels are created using push, and removed using pop. 

    Assertions may be "committed". Whenever a push is executed, all
    "uncommitted" assertions are automatically committed. 
    Only uncommitted assertions can be simplified/reduced.

    An assertion set has a limited model converter that only supports
    definitions (for variable/function elimination) and filters (for fresh
    symbols introduced by tactics).

    Some tactics support assertion_stacks and can be applied to them.
    However, a tactic can only access the assertions on the top level.
    The assertion stack also informs the tactic which declarations 
    can't be eliminated since they occur in the already committed part. 
    
Author:

    Leonardo de Moura (leonardo) 2012-02-17

Revision History:

--*/
#ifndef _ASSERTION_STACK_H_
#define _ASSERTION_STACK_H_

#include"ast.h"
#include"model.h"
#include"expr_substitution.h"
#include"macro_substitution.h"

class assertion_stack {
    ast_manager &                m_manager;
    unsigned                     m_ref_count;
    bool                         m_models_enabled;  // model generation is enabled.
    bool                         m_proofs_enabled;  // proof production is enabled. m_manager.proofs_enabled() must be true if m_proofs_enabled == true
    bool                         m_core_enabled;    // unsat core extraction is enabled.
    bool                         m_inconsistent; 
    ptr_vector<expr>             m_forms;
    ptr_vector<proof>            m_proofs;
    ptr_vector<expr_dependency>  m_deps;
    unsigned                     m_form_qhead; // position of first uncommitted assertion
    unsigned                     m_mc_qhead;

    // Set of declarations that can't be eliminated
    obj_hashtable<func_decl>     m_forbidden_set;
    func_decl_ref_vector         m_forbidden;
    
    // Limited model converter support, it supports only extensions
    // and filters.
    // It should be viewed as combination of extension_model_converter and 
    // filter_model_converter for goals.
    expr_substitution            m_csubst;  // substitution for eliminated constants
    macro_substitution           m_fsubst;  // substitution for eliminated functions

    // Model converter is just a sequence of tagged pointers.
    // Tag 0 (extension) func_decl was eliminated, and its definition is in m_vsubst or m_fsubst.
    // Tag 1 (filter) func_decl was introduced by tactic, and must be removed from model.
    ptr_vector<func_decl>        m_mc;      
    
    struct scope {
        unsigned                 m_forms_lim;
        unsigned                 m_forbidden_vars_lim;
        unsigned                 m_mc_lim;
        bool                     m_inconsistent_old;
    };
    
    svector<scope>               m_scopes;

    void init(bool proofs_enabled, bool models_enabled, bool core_enabled);
    void expand(expr * f, proof * pr, expr_dependency * dep, expr_ref & new_f, proof_ref & new_pr, expr_dependency_ref & new_dep);
    void push_back(expr * f, proof * pr, expr_dependency * d);
    void quick_process(bool save_first, expr * & f, expr_dependency * d);
    void process_and(bool save_first, app * f, proof * pr, expr_dependency * d, expr_ref & out_f, proof_ref & out_pr);
    void process_not_or(bool save_first, app * f, proof * pr, expr_dependency * d, expr_ref & out_f, proof_ref & out_pr);
    void slow_process(bool save_first, expr * f, proof * pr, expr_dependency * d, expr_ref & out_f, proof_ref & out_pr);
    void slow_process(expr * f, proof * pr, expr_dependency * d);

public:
    assertion_stack(ast_manager & m, bool models_enabled = true, bool core_enabled = true);
    assertion_stack(ast_manager & m, bool proofs_enabled, bool models_enabled, bool core_enabled);
    ~assertion_stack();

    void reset();

    void inc_ref() { ++m_ref_count; }
    void dec_ref() { --m_ref_count; if (m_ref_count == 0) dealloc(this); }
    
    ast_manager & m() const { return m_manager; }
    
    bool models_enabled() const { return m_models_enabled; }
    bool proofs_enabled() const { return m_proofs_enabled; }
    bool unsat_core_enabled() const { return m_core_enabled; }
    bool inconsistent() const { return m_inconsistent; }
    
    unsigned size() const { return m_forms.size(); }
    unsigned qhead() const { return m_form_qhead; }
    expr * form(unsigned i) const { return m_forms[i]; }
    proof * pr(unsigned i) const { return proofs_enabled() ? static_cast<proof*>(m_proofs[i]) : 0; }
    expr_dependency * dep(unsigned i) const { return unsat_core_enabled() ? m_deps[i] : 0; }
    
    void assert_expr(expr * f, proof * pr, expr_dependency * d);
    void assert_expr(expr * f) {
        assert_expr(f, proofs_enabled() ? m().mk_asserted(f) : 0, 0);
    }
    void update(unsigned i, expr * f, proof * pr = 0, expr_dependency * dep = 0);
    void expand_and_update(unsigned i, expr * f, proof * pr = 0, expr_dependency * d = 0);
    
    void commit();
    void push();
    void pop(unsigned num_scopes);
    unsigned scope_lvl() const { return m_scopes.size(); }
  
    bool is_well_sorted() const;

    bool is_forbidden(func_decl * f) const { return m_forbidden_set.contains(f); }
    void add_filter(func_decl * f) const;
    void add_definition(app * c, expr * def, proof * pr, expr_dependency * dep);
    void add_definition(func_decl * f, quantifier * q, proof * pr, expr_dependency * dep);

    void convert(model_ref & m);

    void display(std::ostream & out) const;
};

#endif
