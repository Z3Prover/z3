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

reslimit::reslimit():
    m_cancel(0),
    m_suspend(false),
    m_count(0),
    m_limit(0) {
}

uint64_t reslimit::count() const {
    return m_count;
}

bool reslimit::inc() {
    ++m_count;
    bool r = (m_cancel == 0 && (m_limit == 0 || m_count <= m_limit)) || m_suspend;
    return r;
}

bool reslimit::inc(unsigned offset) {
    m_count += offset;
    bool r = (m_cancel == 0 && (m_limit == 0 || m_count <= m_limit)) || m_suspend;
    return r;
}

void reslimit::push(unsigned delta_limit) {
    uint64_t new_limit = delta_limit + m_count;
    if (new_limit <= m_count) {
        new_limit = 0;
    }
    m_limits.push_back(m_limit);
    m_limit = m_limit==0 ? new_limit : std::min(new_limit, m_limit);
    m_cancel = 0;
}

void reslimit::pop() {
    if (m_count > m_limit && m_limit > 0) {
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
    m_children.pop_back();    
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
    set_cancel(m_cancel+1);    
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
