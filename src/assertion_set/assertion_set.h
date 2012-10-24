/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    assertion_set.h

Abstract:

    Assertion set.

Author:

    Leonardo de Moura (leonardo) 2011-04-20

Revision History:

--*/
#ifndef _ASSERTION_SET_H_
#define _ASSERTION_SET_H_

#include"ast.h"
#include"ast_translation.h"
#include"for_each_expr.h"

class cmd_context;

class assertion_set {
    ast_manager & m_manager;
    bool          m_inconsistent;
    expr_array    m_forms;
    expr_array    m_proofs;

    void push_back(expr * f, proof * pr);
    void quick_process(bool save_first, expr * & f);
    void process_and(bool save_first, app * f, proof * pr, expr_ref & out_f, proof_ref & out_pr);
    void process_not_or(bool save_first, app * f, proof * pr, expr_ref & out_f, proof_ref & out_pr);
    void slow_process(bool save_first, expr * f, proof * pr, expr_ref & out_f, proof_ref & out_pr);
    void slow_process(expr * f, proof * pr);

public:
    assertion_set(ast_manager & m):m_manager(m), m_inconsistent(false) {}
    ~assertion_set() { reset(); }

    ast_manager & m() const { return m_manager; }

    bool inconsistent() const { return m_inconsistent; }

    void reset();

    void copy(assertion_set & target) const;

    void assert_expr(expr * f, proof * pr);
    
    void assert_expr(expr * f) {
        assert_expr(f, m().mk_asserted(f));
    }
    
    unsigned size() const { return m().size(m_forms); }

    unsigned num_exprs() const;
  
    expr * form(unsigned i) const { return m().get(m_forms, i); }
    
    proof * pr(unsigned i) const { return m().proofs_enabled() ? static_cast<proof*>(m().get(m_proofs, i)) : 0; }
    
    void update(unsigned i, expr * f, proof * pr = 0);
    
    void elim_true();

    void elim_redundancies();

    void display(cmd_context & ctx, std::ostream & out) const;

    void display(cmd_context & ctx) const;

    void display(std::ostream & out) const;

    void display_ll(std::ostream & out) const;

    void display_as_and(std::ostream & out) const;

    void display_dimacs(std::ostream & out) const;

    assertion_set * translate(ast_translation & translator) const;
};

void assert_exprs_from(cmd_context const & ctx, assertion_set & t);

template<typename ForEachProc>
void for_each_expr_as(ForEachProc& proc, assertion_set const& s) {
    expr_mark visited;
    for (unsigned i = 0; i < s.size(); ++i) {
        for_each_expr(proc, visited, s.form(i));
    }
}

#endif
