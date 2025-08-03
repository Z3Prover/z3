/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    cancel_eh.h

Abstract:

    Template for implementing simple event handler that just invokes cancel method.

Author:

    Leonardo de Moura (leonardo) 2011-04-27.

Revision History:

--*/
#pragma once

#include <atomic>
#include <mutex>
#include "util/event_handler.h"

/**
   \brief Generic event handler for invoking cancel method.
*/
template<typename T>
class cancel_eh : public event_handler {
    std::mutex m_mutex;
    std::atomic<bool> m_canceled = false;
    bool m_auto_cancel = false;
    T & m_obj;
public:
    cancel_eh(T & o): m_obj(o) {}
    ~cancel_eh() override { if (m_canceled) m_obj.dec_cancel(); if (m_auto_cancel) m_obj.auto_cancel(); }

    // Note that this method doesn't race with the destructor since
    // potential callers like scoped_ctrl_c/scoped_timer are destroyed
    // before the cancel_eh destructor is invoked.
    // Thus, the only races are with itself and with the getters.
    void operator()(event_handler_caller_t caller_id) override {
        std::lock_guard lock(m_mutex);
        if (!m_canceled) {
            m_caller_id = caller_id;
            m_obj.inc_cancel();
            m_canceled = true;
        }
    }

    bool canceled() const { return m_canceled; }
    void reset() { m_canceled = false; }
    T& t() { return m_obj; }
    void set_auto_cancel() { m_auto_cancel = true; }
};
