/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    event_handler.h

Abstract:

    Abstract event handler.

Author:

    Leonardo de Moura (leonardo) 2011-04-26.

Revision History:

--*/
#pragma once

enum event_handler_caller_t {
    UNSET_EH_CALLER,
    CTRL_C_EH_CALLER,
    TIMEOUT_EH_CALLER,
    RESLIMIT_EH_CALLER,
    API_INTERRUPT_EH_CALLER
};

class event_handler {
protected:
    event_handler_caller_t m_caller_id;
public:
    event_handler(): m_caller_id(UNSET_EH_CALLER) {}
    virtual ~event_handler() {}
    virtual void operator()(event_handler_caller_t caller_id) = 0;
    event_handler_caller_t caller_id() const { return m_caller_id; }
};

