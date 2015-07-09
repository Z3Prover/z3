/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    sls_powers.h

Abstract:

    Power-of-2 module for SLS

Author:

    Christoph (cwinter) 2012-02-29

Notes:

--*/

#ifndef SLS_POWERS_H_
#define SLS_POWERS_H_

#include"mpz.h"

class powers : public u_map<mpz*> {
    unsynch_mpz_manager & m;
public:
    powers(unsynch_mpz_manager & m) : m(m) {}
    ~powers() {
        for (iterator it = begin(); it != end(); it++) {
            m.del(*it->m_value);
            dealloc(it->m_value);
        }
    }

    const mpz & operator()(unsigned n) {
        u_map<mpz*>::iterator it = find_iterator(n);
        if (it != end())
            return *it->m_value;
        else {
            mpz * new_obj = alloc(mpz);                        
            m.mul2k(m.mk_z(1), n, *new_obj);
            insert(n, new_obj);
            return *new_obj;
        }
    }
};  

#endif