/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    spc_der.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-02-17.

Revision History:

--*/
#ifndef _SPC_DER_H_
#define _SPC_DER_H_

#include"spc_clause.h"

namespace spc {

    /**
       \brief Functor for applying destructive equality resolution.
       This is similar to the Functor in der.h, but this one applies
       the simplification on clauses instead of ast's.

       x != s or R
       ==>
       sigma(R)
       
       where
       sigma = mgu(x, s)
    */
    class der { 
        ast_manager &   m_manager;
        substitution    m_subst;
        unsigned_vector m_to_keep;
        family_id       m_spc_fid;
        void apply(clause * cls, unsigned j, expr * lhs, expr * rhs);
        bool apply(clause * cls);
    public:
        der(ast_manager & m);
        void operator()(clause * cls);
    };
};

#endif /* _SPC_DER_H_ */

