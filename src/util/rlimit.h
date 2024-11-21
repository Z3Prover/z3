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
#include "util/timer.h"
#include <atomic>

void initialize_rlimit();
void finalize_rlimit();
/*
  ADD_INITIALIZER('initialize_rlimit();')
  ADD_FINALIZER('finalize_rlimit();')
*/

class reslimit {
    std::atomic<unsigned> m_cancel = 0;
    bool                  m_suspend = false;
    uint64_t              m_count = 0;
    uint64_t              m_limit = std::numeric_limits<uint64_t>::max();
#ifdef POLLING_TIMER
    timer                 m_timer;
    unsigned              m_timeout_ms = 0;
    unsigned              m_num_timers = 0;
#endif
    svector<uint64_t>     m_limits;
    ptr_vector<reslimit>  m_children;
    

    void set_cancel(unsigned f);
    friend class scoped_suspend_rlimit;

#ifdef POLLING_TIMER
    bool is_timeout() { return m_timer.ms_timeout(m_timeout_ms) && (inc_cancel(m_num_timers), pop_timeout(), true); }  
    void inc_cancel(unsigned k);
#else
    inline bool is_timeout() { return false; }
#endif

#ifdef POLLING_TIMER

    void pop_timeout() {
        m_timeout_ms = 0;
    }

    void push_timeout(unsigned ms);
#endif

public:
    reslimit();
    void push(unsigned delta_limit);
    void pop();
    void push_child(reslimit* r);
    void pop_child();
    void pop_child(reslimit* r);

    bool inc();
    bool inc(unsigned offset);
    uint64_t count() const;
    void reset_count() { m_count = 0; }

#ifdef POLLING_TIMER
    void set_timeout(unsigned ms) { push_timeout(ms);  }
#endif
    bool suspended() const { return m_suspend; }
    inline bool not_canceled() { 
        return m_suspend || (m_cancel == 0 && m_count <= m_limit && !is_timeout()); 
    }
    inline bool is_canceled()  { return !not_canceled(); }
    char const* get_cancel_msg() const;
    void cancel();
    void reset_cancel();

    void inc_cancel();
    void dec_cancel();
    void auto_cancel();
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
    unsigned   m_sz = 0;
    scoped_limits(reslimit& lim): m_limit(lim) {}    
    ~scoped_limits() { reset(); }
    void reset() { for (unsigned i = 0; i < m_sz; ++i) m_limit.pop_child(); m_sz = 0; }
    void push_child(reslimit* lim) { m_limit.push_child(lim); ++m_sz; }
};
