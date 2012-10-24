/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    spc_rewriter.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-02-11.

Revision History:

--*/
#ifndef _SPC_REWRITER_H_
#define _SPC_REWRITER_H_

#include"simplifier.h"
#include"order.h"
#include"substitution_tree.h"
#include"spc_clause.h"
#include"spc_asserted_literals.h"
#include"sparse_use_list.h"

namespace spc {
    
    /**
       \brief Apply rewriting steps using demodulation rule:

       C[s] ==> C[sigma(r)]
       when 
       
       l = r is a known equality (demodulator)
       sigma(l) = s
       sigma(l) > sigma(r)

       It also applies the following rules:
       
       - Duplicate literal deletion

       - Resolved literal deletion

       - Positive simplify reflect
       s = t,  (u[p <- sigma(s)] != u[p <- sigma(t)] or R)
       ==>
       R
   
       - Negative simplify reflect
       s != t  (sigma(s = t) or R)
       ===>
       R
    */
    class rewriter : public simplifier {
    protected:
        typedef sparse_use_list<expr, ptr_vector<clause> > clause_use_list;
        asserted_literals &       m_asserted_literals;
        order &                   m_order;
        family_id                 m_spc_fid;

        substitution              m_subst;
        substitution_tree         m_st; // index for potential demodulators left-hand-side
        clause_use_list           m_cls_use_list; // index for demodulators left-hand-side to equation.
        found_literals            m_found_literals;

        ptr_vector<justification> m_justifications;

        struct visitor : public st_visitor {
            ast_manager &     m_manager;
            order &           m_order;
            clause_use_list & m_cls_use_list;
            bool              m_found;
            clause *          m_clause;
            expr *            m_source;
            expr *            m_target;

            visitor(order & ord, substitution & subst, clause_use_list & ul):
                st_visitor(subst), m_manager(ord.get_manager()), m_order(ord), m_cls_use_list(ul) {
            }
            
            virtual bool operator()(expr * e);
        };

        unsigned                  m_max_scope_lvl; // maximal scope level used during rewrite.
        visitor                   m_visitor;

        proof * mk_demodulation_proof(expr * old_expr, expr * new_expr, proof * parent);

        bool demodulator(clause * cls) const;
        void insert(clause * cls, expr * source);
        void erase(clause * cls, expr * source);
        void reserve_vars(unsigned num_vars);
        void reserve_offsets(unsigned num_offsets);
        void save_justification(justification * j);

        void reduce_literal(literal const & l, literal & l_r, proof * & l_pr);

    public:
        rewriter(ast_manager & m, simplifier & s, order & ord, asserted_literals & al);
        virtual ~rewriter();
        
        /**
           \brief Insert clause into rewriter indexes
        */
        void insert(clause * cls);

        /**
           \brief Remove clause from rewriter indexes
        */
        void erase(clause * cls);
        
        clause * operator()(clause * cls);

        void reset();
    };
};

#endif /* _SPC_REWRITER_H_ */

