/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    spc_asserted_literals.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-02-14.

Revision History:

--*/
#ifndef _SPC_ASSERTED_LITERALS_H_
#define _SPC_ASSERTED_LITERALS_H_

#include"spc_clause.h"
#include"substitution_tree.h"
#include"obj_hashtable.h"

namespace spc {
    
    /**
       \brief Index for the asserted literals in the logical context.
       
       This index is used to implement forward unit subsumption, 
       equality subsumption, positive simplify-reflect, and
       negative simplify-reflect.
    */
    class asserted_literals {
    protected:
        typedef obj_map<expr, clause*> expr2clause;
        ast_manager &       m_manager;
        substitution_tree * m_st[2];
        expr2clause *       m_expr2clause[2];
        substitution        m_subst;
        tmp_app             m_tmp_eq1;
        tmp_app             m_tmp_eq2;
    public:
        asserted_literals(ast_manager & m);
        ~asserted_literals();

        void insert(clause * cls);
        void erase(clause * cls);
        void reset();
        void reserve_vars(unsigned num_vars) { m_subst.reserve_vars(num_vars); }

        clause * gen(literal const & l) {
            return gen(l.atom(), l.sign());
        }

        clause * gen(expr * atom, bool neg);
        clause * gen_eq(expr * lhs, expr * rhs);
        clause * subsumes(expr * lhs, expr * rhs);

        bool has_pos_literals() const { return !m_st[0]->empty(); }
        bool has_neg_literals() const { return !m_st[1]->empty(); }
        bool has_literals() const { return has_pos_literals() || has_neg_literals(); }
    };
    
};

#endif /* _SPC_ASSERTED_LITERALS_H_ */

