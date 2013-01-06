/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    api_rcf.h

Abstract:

    Additional APIs for handling elements of the Z3 real closed field that contains:
       - transcendental extensions
       - infinitesimal extensions
       - algebraic extensions

Author:

    Leonardo de Moura (leonardo) 2012-01-05

Notes:
    
--*/
#ifndef _API_RCF_H_
#define _API_RCF_H_

#include"api_util.h"
#include"realclosure.h"

struct Z3_rcf_num_ref : public api::object {
    rcnumeral m_num;
    virtual ~Z3_rcf_num_ref() {}
};


inline Z3_rcf_num_ref * to_rcf_num(Z3_rcf_num n) { return reinterpret_cast<Z3_rcf_num_ref *>(n); }
inline Z3_rcf_num of_rcf_num(Z3_rcf_num_ref * n) { return reinterpret_cast<Z3_rcf_num>(n); }
inline rcnumeral & to_rcnumeral(Z3_rcf_num n) { SASSERT(n != 0); return to_rcf_num(n)->m_num; }

#endif
