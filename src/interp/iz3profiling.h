/*++
  Copyright (c) 2011 Microsoft Corporation

  Module Name:

  iz3profiling.h

  Abstract:

  Some routines for measuring performance.

  Author:

  Ken McMillan (kenmcmil)

  Revision History:

  --*/

#ifndef IZ3PROFILING_H
#define IZ3PROFILING_H

#include <ostream>

namespace profiling {
    /** Start a timer with given name */
    void timer_start(const char *);
    /** Stop a timer with given name */
    void timer_stop(const char *);
    /** Print out timings */
    void print(std::ostream &s);
    /** Show the current time. */
    void show_time();
}

#endif

