/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    timeit.h

Abstract:

    Support for timers.

Author:

    Nikolaj Bjorner (nbjorner) 2006-09-22

Revision History:

    Leonardo de Moura (leonardo) 2011-04-27
    Rewrote using stopwatches, added support for tracking memory

--*/
#pragma once

class timeit {
    struct imp;
    imp *  m_imp;
public:
    timeit(bool enable, char const * msg, std::ostream & out = std::cerr);
    ~timeit();
};

