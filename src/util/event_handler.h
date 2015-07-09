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
#ifndef EVENT_HANDLER_H_
#define EVENT_HANDLER_H_

class event_handler {
public:
    virtual ~event_handler() {}
    virtual void operator()() = 0;
};

#endif
