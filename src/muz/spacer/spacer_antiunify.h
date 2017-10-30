/*++
Copyright (c) 2017 Arie Gurfinkel

Module Name:

    spacer_antiunify.h

Abstract:

  Antiunification utilities

Author:

    Bernhard Gleiss
    Arie Gurfinkel

Revision History:

--*/

#ifndef _SPACER_ANTIUNIFY_H_
#define _SPACER_ANTIUNIFY_H_

#include "ast/ast.h"

namespace spacer {
class anti_unifier
{
public:
    anti_unifier(expr* t, ast_manager& m);
    ~anti_unifier() {}

    bool add_term(expr* t);
    void finalize();

    expr* get_generalization() {return m_g;}
    unsigned get_num_substitutions() {return m_substitutions.size();}
    obj_map<expr, expr*> get_substitution(unsigned index){
        SASSERT(index < m_substitutions.size());
        return m_substitutions[index];
    }

private:
    ast_manager& m;
    // tracking all created expressions
    expr_ref_vector m_pinned;

    expr_ref m_g;

    vector<obj_map<expr, expr*>> m_substitutions;
};

class naive_convex_closure
{
public:
    static bool compute_closure(anti_unifier& au, ast_manager& m,
                                expr_ref& result);

private:
    static bool get_range(vector<unsigned>& v, unsigned& lower_bound,
                          unsigned& upper_bound);
    static void substitute_vars_by_const(ast_manager& m, expr* t, expr* c,
                                         expr_ref& res);
};

}
#endif
