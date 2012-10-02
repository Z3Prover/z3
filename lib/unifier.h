/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    unifier.h

Abstract:

    Quasi-linear unification.

Author:

    Leonardo de Moura (leonardo) 2008-01-28.

Revision History:

--*/
#ifndef _UNIFIER_H_
#define _UNIFIER_H_

#include"ast.h"
#include"substitution.h"

/**
   \brief Functor for unifying expressions.
   It implements a quasi-linear unification algorithm.

   It has support for two different variable banks: left and right.
   That is, variable i in left bank is considered different from
   variable i in the right bank.  This feature allows us to avoid
   unnecessary variable renaming.
*/
class unifier {
    typedef std::pair<expr_offset, expr_offset> entry;
    
    ast_manager &                m_manager;
    substitution *               m_subst;
    
    svector<entry>               m_todo;
    expr_offset_map<expr_offset> m_find;
    expr_offset_map<unsigned>    m_size;

    bool                         m_last_call_succeeded;

    expr_offset find(expr_offset n);
    void save_var(expr_offset const & p, expr_offset const & t);
    void union1(expr_offset const & n1, expr_offset const & n2);
    void union2(expr_offset n1, expr_offset n2);
    void reset(unsigned num_offsets);

    bool unify_core(expr_offset p1, expr_offset p2);
    
public:
    unifier(ast_manager & m):m_manager(m), m_last_call_succeeded(false) {}

    /**
       \brief Unify the given expressions. Return true if succeeded,
       and store the result in the given substitution.
       
       If use_offsets is true, then the variables in the given expressions are assumed to be 
       in different banks.
    */
    bool operator()(unsigned num_exprs, expr ** es, substitution & s, bool use_offsets = true);

    bool operator()(expr * e1, expr * e2, substitution & s, bool use_offsets = true);
};

#endif /* _UNIFIER_H_ */

