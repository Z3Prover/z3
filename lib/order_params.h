/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    order_params.h

Abstract:

    Term ordering parameters.

Author:

    Leonardo de Moura (leonardo) 2008-01-28.

Revision History:

--*/
#ifndef _ORDER_PARAMS_H_
#define _ORDER_PARAMS_H_

#include"ini_file.h"

enum order_kind {
    ORD_KBO,
    ORD_LPO
};

struct order_params {
    svector<symbol>          m_order_precedence;
    svector<symbol>          m_order_precedence_gen;
    svector<symbol_nat_pair> m_order_weights;
    unsigned                 m_order_var_weight;
    order_kind               m_order_kind;
    
    order_params():
        m_order_var_weight(1),
        m_order_kind(ORD_KBO) {
    }

    void register_params(ini_params & p);
};

#endif /* _ORDER_PARAMS_H_ */
