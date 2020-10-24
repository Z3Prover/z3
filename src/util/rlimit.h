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
#pragma once

#include "util/vector.h"
#include <atomic>

void initialize_rlimit();
void finalize_rlimit();
/*
  ADD_INITIALIZER('initialize_rlimit();')
  ADD_FINALIZER('finalize_rlimit();')
*/

class reslimit {
    std::atomic<unsigned> m_cancel;
    bool            m_suspend;
    uint64_t        m_count;
    uint64_t        m_limit;
    svector<uint64_t> m_limits;
    ptr_vector<reslimit> m_children;

    void set_cancel(unsigned f);
    friend class scoped_suspend_rlimit;

public:
    reslimit();
    void push(unsigned delta_limit);
    void pop();
    void push_child(reslimit* r);
    void pop_child();

    bool inc();
    bool inc(unsigned offset);
    uint64_t count() const;

    bool suspended() const { return m_suspend;  }
    inline bool not_canceled() const { return (m_cancel == 0 && m_count <= m_limit) || m_suspend; }
    inline bool is_canceled() const { return !not_canceled(); }
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

class scoped_suspend_rlimit {
    reslimit & m_limit;
    bool       m_suspend;
public:
    scoped_suspend_rlimit(reslimit& r): m_limit(r) {
        m_suspend = r.m_suspend;
        r.m_suspend = true;
    }

    scoped_suspend_rlimit(reslimit& r, bool do_suspend): m_limit(r) {
        m_suspend = r.m_suspend;
        r.m_suspend |= do_suspend;
    }
    ~scoped_suspend_rlimit() {
        m_limit.m_suspend = m_suspend;
    }
};

struct scoped_limits {
    reslimit&  m_limit;
    unsigned   m_sz;
    scoped_limits(reslimit& lim): m_limit(lim), m_sz(0) {}
    ~scoped_limits() { for (unsigned i = 0; i < m_sz; ++i) m_limit.pop_child(); }
    void push_child(reslimit* lim) { m_limit.push_child(lim); ++m_sz; }
};
