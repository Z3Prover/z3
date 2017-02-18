/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    arith_simplifier_params.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-05-09.

Revision History:

--*/
#ifndef ARITH_SIMPLIFIER_PARAMS_H_
#define ARITH_SIMPLIFIER_PARAMS_H_

#include"params.h"

struct arith_simplifier_params { 
    bool    m_arith_expand_eqs;
    bool    m_arith_process_all_eqs;

    arith_simplifier_params(params_ref const & p = params_ref()) {
        updt_params(p);
    }

    void updt_params(params_ref const & _p);

    void display(std::ostream & out) const;
};
    
#endif /* ARITH_SIMPLIFIER_PARAMS_H_ */

