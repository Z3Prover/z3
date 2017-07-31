/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    scoped_timer.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2011-04-26.

Revision History:

--*/
#ifndef SCOPED_TIMER_H_
#define SCOPED_TIMER_H_

#include "util/event_handler.h"

class scoped_timer {
    struct imp;
    imp *  m_imp;
public:
    scoped_timer(unsigned ms, event_handler * eh);
    ~scoped_timer();
};

#endif
