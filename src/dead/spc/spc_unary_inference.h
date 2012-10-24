/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    spc_unary_inference.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-02-14.

Revision History:

--*/
#ifndef _SPC_UNARY_INFERENCE_H_
#define _SPC_UNARY_INFERENCE_H_

#include"spc_clause.h"
#include"unifier.h"

namespace spc {

    /**
       \brief Superclass for eq_resolution and factoring.
    */
    class unary_inference {
    protected:
        ast_manager & m_manager;
        order &       m_order;
        substitution  m_subst;
        unifier       m_unifier; 
        
        clause * mk_result(clause * cls, unsigned j);
        virtual justification * mk_justification(justification * parent, unsigned num_lits, literal * new_lits) = 0;
    public:
        unary_inference(ast_manager & m, order & ord);
        virtual ~unary_inference() {}
    };

};


#endif /* _SPC_UNARY_INFERENCE_H_ */

