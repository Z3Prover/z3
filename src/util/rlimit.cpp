/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    rlimit.cpp

Abstract:

    Resource limit container.

Author:

    Nikolaj Bjorner (nbjorner) 2015-09-28

Revision History:

--*/
#include "util/rlimit.h"
#include "util/common_msgs.h"
#include "util/mutex.h"


static DECLARE_MUTEX(g_rlimit_mux);

void initialize_rlimit() {
    ALLOC_MUTEX(g_rlimit_mux);
}

void finalize_rlimit() {
    DEALLOC_MUTEX(g_rlimit_mux);
}

reslimit::reslimit() {
}

uint64_t reslimit::count() const {
    return m_count;
}

bool reslimit::inc() {
    ++m_count;
    return not_canceled();
}

bool reslimit::inc(unsigned offset) {
    m_count += offset;
    return not_canceled();
}

void reslimit::push(unsigned delta_limit) {
    uint64_t new_limit = delta_limit ? delta_limit + m_count : std::numeric_limits<uint64_t>::max();
    if (new_limit <= m_count) {
        new_limit = std::numeric_limits<uint64_t>::max();
    }
    m_limits.push_back(m_limit);
    m_limit = std::min(new_limit, m_limit);
    m_cancel = 0;
}

void reslimit::pop() {
    if (m_count > m_limit) {
        m_count = m_limit;
    }
    m_limit = m_limits.back();
    m_limits.pop_back();
    m_cancel = 0;
}

char const* reslimit::get_cancel_msg() const {
    if (m_cancel > 0) {
        return Z3_CANCELED_MSG;
    }
    else {
        return Z3_MAX_RESOURCE_MSG;
    }
}

void reslimit::push_child(reslimit* r) {
    lock_guard lock(*g_rlimit_mux);
    m_children.push_back(r);    
}

void reslimit::pop_child() {
    lock_guard lock(*g_rlimit_mux);
    m_count += m_children.back()->m_count;
    m_children.back()->m_count = 0;
    m_children.pop_back();    
}

void reslimit::pop_child(reslimit* r) {
    lock_guard lock(*g_rlimit_mux);
    for (unsigned i = 0; i < m_children.size(); ++i) {
        if (m_children[i] == r) {
            m_count += r->m_count;
            r->m_count = 0;
            m_children.erase(m_children.begin() + i);
            return;
        }
    }
}


void reslimit::cancel() {
    lock_guard lock(*g_rlimit_mux);
    set_cancel(m_cancel+1);    
}

void reslimit::reset_cancel() {
    lock_guard lock(*g_rlimit_mux);
    set_cancel(0);    
}

void reslimit::inc_cancel() {
    lock_guard lock(*g_rlimit_mux);
    set_cancel(m_cancel + 1);
}

void reslimit::dec_cancel() {
    lock_guard lock(*g_rlimit_mux);
    if (m_cancel > 0) {
        set_cancel(m_cancel-1);
    }
}

void reslimit::set_cancel(unsigned f) {
    m_cancel = f;
    for (unsigned i = 0; i < m_children.size(); ++i) {
        m_children[i]->set_cancel(f);
    }
}



#ifdef POLLING_TIMER
void reslimit::push_timeout(unsigned ms) {
    m_num_timers++;
    if (m_cancel > 0) {
        ++m_cancel;
        return;
    }
    if (m_timeout_ms != 0) {
        double ms_taken = 1000 * m_timer.get_seconds();
        if (ms_taken > m_timeout_ms)
            return;
        if (m_timeout_ms - ms_taken < ms)
            return;
    }
    m_timer = timer();
    m_timeout_ms = ms;
}

void reslimit::inc_cancel(unsigned k) {
    lock_guard lock(*g_rlimit_mux);
    set_cancel(m_cancel + k);        
}

void reslimit::auto_cancel() {
    --m_num_timers;
    dec_cancel();
}

#else
void reslimit::auto_cancel() {
    UNREACHABLE();
}
#endif