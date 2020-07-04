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

#include "util/event_handler.h"

/**
   \brief Generic event handler for invoking cancel method.
*/
template<typename T>
class cancel_eh : public event_handler {
    bool m_canceled;
    T & m_obj;
public:
    cancel_eh(T & o): m_canceled(false), m_obj(o) {}
    ~cancel_eh() override { if (m_canceled) m_obj.dec_cancel(); }
    void operator()(event_handler_caller_t caller_id) override {
        if (!m_canceled) {
            m_caller_id = caller_id;
            m_canceled = true;
            m_obj.inc_cancel(); 
        }
    }
    bool canceled() const { return m_canceled; }
    void reset() { m_canceled = false; }
};

