/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    rlimit.h

Abstract:

    Resource limit container.

Author:

    Nikolaj Bjorner (nbjorner) 2015-09-28

Revision History:

--*/
#ifndef RLIMIT_H_
#define RLIMIT_H_

#include "vector.h"

class reslimit {
    unsigned        m_count;
    unsigned        m_limit;
    unsigned_vector m_limits;
public:    
    reslimit();
    bool inc();
    bool inc(unsigned offset);
    void push(unsigned delta_limit);
    void pop();
    unsigned count() const; 
};

class scoped_rlimit {
    reslimit& m_limit;
public:
    scoped_rlimit(reslimit& r, unsigned l): m_limit(r) {
        r.push(l);
    }
    ~scoped_rlimit() { m_limit.pop(); }

};

#endif
