/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    scoped_ctrl_c.h

Abstract:

    Scoped control-c handler.

Author:

    Leonardo de Moura (leonardo) 2011-04-27.

Revision History:

--*/
#pragma once

#include "util/event_handler.h"
#include "util/util.h"

struct scoped_ctrl_c {
    event_handler & m_cancel_eh;
    bool m_enabled;
public:
    // if enabled == false, then scoped_ctrl_c is a noop
    scoped_ctrl_c(event_handler & eh, bool enabled = true);
    ~scoped_ctrl_c();
};
