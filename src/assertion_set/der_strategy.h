/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    der_strategy.h

Abstract:

    DER strategy

Author:

    Leonardo de Moura (leonardo) 2012-10-20

--*/
#ifndef _DER_STRATEGY_H_
#define _DER_STRATEGY_H_

#include"der.h"
#include"assertion_set_strategy.h"

// TODO: delete obsolete class
class der_strategy : public assertion_set_strategy {
    struct     imp;
    imp *      m_imp;
public:
    der_strategy(ast_manager & m);
    virtual ~der_strategy();

    void operator()(assertion_set & s);
    
    virtual void operator()(assertion_set & s, model_converter_ref & mc) {
        operator()(s);
        mc = 0;
    }

    virtual void cleanup();
    virtual void set_cancel(bool f);
};

inline as_st * mk_der(ast_manager & m) {
    return alloc(der_strategy, m);
}


#endif
