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
    volatile unsigned   m_cancel;
    uint64          m_count;
    uint64          m_limit;
    svector<uint64> m_limits;
    ptr_vector<reslimit> m_children;

    void set_cancel(unsigned f);

public:
    reslimit();
    void push(unsigned delta_limit);
    void pop();
    void push_child(reslimit* r);
    void pop_child();

    bool inc();
    bool inc(unsigned offset);
    uint64 count() const;


    bool get_cancel_flag() const { return m_cancel > 0; }
    char const* get_cancel_msg() const;
    void cancel();
    void reset_cancel();

    void inc_cancel();
    void dec_cancel();
};

class scoped_rlimit {
    reslimit& m_limit;
public:
    scoped_rlimit(reslimit& r, unsigned l): m_limit(r) {
        r.push(l);
    }
    ~scoped_rlimit() { m_limit.pop(); }

};

struct scoped_limits {
    reslimit&  m_limit;
    unsigned   m_sz;
    scoped_limits(reslimit& lim): m_limit(lim), m_sz(0) {}
    ~scoped_limits() { for (unsigned i = 0; i < m_sz; ++i) m_limit.pop_child(); }
    void push_child(reslimit* lim) { m_limit.push_child(lim); ++m_sz; }
};


#endif
