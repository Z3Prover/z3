/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    cnf_params.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-01-23.

Revision History:

--*/
#ifndef _CNF_PARAMS_H_
#define _CNF_PARAMS_H_

#include"ini_file.h"

/**
   \brief CNF translation mode.  The cheapest mode is CNF_QUANT, and
   the most expensive is CNF_FULL.
*/
enum cnf_mode {
    CNF_DISABLED, /* CNF translator is disabled. 
                     This mode is sufficient when using E-matching.
                  */
    CNF_QUANT, /* A subformula is put into CNF if it is inside of a
                  quantifier.
               
                  This mode is sufficient when using Superposition
                  Calculus.
               */
    CNF_OPPORTUNISTIC, /* a subformula is also put in CNF if it is cheap. */
    CNF_FULL /* Everything is put into CNF, new names are introduced
                if it is too expensive. */
};

struct cnf_params {
    cnf_mode m_cnf_mode;
    unsigned m_cnf_factor;
    cnf_params():
        m_cnf_mode(CNF_DISABLED),
        m_cnf_factor(4) {
    }
    
    void register_params(ini_params & p);
};


#endif /* _CNF_PARAMS_H_ */

