/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    spc_factoring.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-02-14.

Revision History:

--*/
#ifndef _SPC_FACTORING_H_
#define _SPC_FACTORING_H_

#include"spc_unary_inference.h"
#include"spc_statistics.h"

namespace spc {

    /**
       \brief Functor for applying factoring.

       - Equality Factoring
       s = t or u = v or R
       ==>
       sigma(t != v or u = v or R)
       
       sigma = mgu(s, u)
       sigma(s) not greater than sigma(t)
       sigma(s = t) is eligible for paramodulation.
       
       - Factoring
       P(t) or P(s) or R
       ==>
       sigma(P(t) or R)

       sigma = mgu(t,s)
       sigma(P(t)) is eligible for resolution.
    */
    class factoring : public unary_inference {
    protected:
        statistics & m_stats;
        family_id    m_spc_fid;
        virtual justification * mk_justification(justification * parent, unsigned num_lits, literal * new_lits) {
            return mk_factoring_justification(m_manager, m_spc_fid, parent, num_lits, new_lits);
        }
        clause * mk_eq_fact_result(clause * cls, unsigned j, expr * lhs, expr * rhs);
        void try_eq_factoring(clause * cls, unsigned j, expr * lhs, expr * rhs, ptr_vector<clause> & new_clauses);
        void try_eq_factoring(clause * cls, unsigned i, ptr_vector<clause> & new_clauses);
        void try_factoring(clause * cls, unsigned j, ptr_vector<clause> & new_clauses);
    public:
        factoring(ast_manager & m, order & ord, statistics & stats):unary_inference(m, ord), m_stats(stats), m_spc_fid(m.get_family_id("spc")) {}
        virtual ~factoring() {}
        void operator()(clause * cls, ptr_vector<clause> & new_clauses);
    };
};

#endif /* _SPC_FACTORING_H_ */

