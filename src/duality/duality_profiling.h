/*++
  Copyright (c) 2011 Microsoft Corporation

  Module Name:

  duality_profiling.h

  Abstract:

  collection performance information for duality

  Author:

  Ken McMillan (kenmcmil)

  Revision History:


  --*/

#ifndef DUALITYPROFILING_H
#define DUALITYPROFILING_H

#include <ostream>

namespace Duality {
    /** Start a timer with given name */
    void timer_start(const char *);
    /** Stop a timer with given name */
    void timer_stop(const char *);
    /** Print out timings */
    void print_profile(std::ostream &s);
    /** Show the current time. */
    void show_time();
}

#endif

