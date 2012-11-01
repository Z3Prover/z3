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
    definitions (for constant elimination) and filters (for fresh
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

class assertion_stack {
    struct imp;
    imp * m_imp;
public:
    assertion_stack(ast_manager & m, bool models_enabled = true, bool core_enabled = true);
    assertion_stack(ast_manager & m, bool proofs_enabled, bool models_enabled, bool core_enabled);
    ~assertion_stack();

    void reset();
    
    ast_manager & m() const;
    
    bool models_enabled() const;
    bool proofs_enabled() const;
    bool unsat_core_enabled() const;
    bool inconsistent() const;
    
    unsigned size() const;
    unsigned qhead() const;
    expr * form(unsigned i) const;
    proof * pr(unsigned i) const;
    expr_dependency * dep(unsigned i) const;
    
    void assert_expr(expr * f, proof * pr, expr_dependency * d);
    void assert_expr(expr * f);
    void update(unsigned i, expr * f, proof * pr = 0, expr_dependency * dep = 0);
    void expand_and_update(unsigned i, expr * f, proof * pr = 0, expr_dependency * d = 0);
    
    void commit();
    void push();
    void pop(unsigned num_scopes);
    unsigned scope_lvl() const;
  
    bool is_well_sorted() const;

    bool is_forbidden(func_decl * f) const;
    void add_filter(func_decl * f);
    void add_definition(app * c, expr * def, proof * pr, expr_dependency * dep);

    void convert(model_ref & m);
    void display(std::ostream & out) const;
};

#endif
