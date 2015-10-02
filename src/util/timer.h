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

class stopwatch;

/**
   \brief Wrapper for the stopwatch class. It hides windows.h dependency.
*/
class timer {
    stopwatch * m_watch;
public:
    timer();
    ~timer();
    void start();
    double get_seconds();
    bool timeout(unsigned secs) { return secs > 0 && get_seconds() > secs; }
    bool ms_timeout(unsigned ms) { return ms > 0 && get_seconds() * 1000 > ms; }
};

#endif /* TIMER_H_ */

