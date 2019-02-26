/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    timer.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2009-01-06.

Revision History:

--*/
#ifndef TIMER_H_
#define TIMER_H_

#include "util/stopwatch.h"

/**
   \brief Wrapper for the stopwatch class.
*/
class timer {
    stopwatch m_watch;
public:
    timer() {
        m_watch.start();
    }

    double get_seconds() const {
        return m_watch.get_current_seconds();
    }

    bool timeout(unsigned secs) const {
        return secs != 0 && secs != UINT_MAX && get_seconds() > secs;
    }

    bool ms_timeout(unsigned ms) const {
        return ms != 0 && ms != UINT_MAX && get_seconds() * 1000 > ms;
    }
};

#endif /* TIMER_H_ */
