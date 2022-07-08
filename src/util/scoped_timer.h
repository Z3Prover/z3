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
#pragma once

#include "util/event_handler.h"

struct scoped_timer_state;

class scoped_timer {
    scoped_timer_state *s = nullptr;
public:
    scoped_timer(unsigned ms, event_handler * eh);
    ~scoped_timer();
    static void initialize();
    static void finalize();
private:
    void init_state(unsigned ms, event_handler * eh);
};

/*
    ADD_INITIALIZER('scoped_timer::initialize();')
*/
