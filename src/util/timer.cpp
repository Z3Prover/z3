/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    timer.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2009-01-06.

Revision History:

--*/
#include "util/util.h"
#include "util/memory_manager.h"
#include "util/stopwatch.h"
#include "util/timer.h"

timer::timer(){
    m_watch = alloc(stopwatch);
    start();
}
 
timer::~timer() {
    dealloc(m_watch);
}

void timer::start() {
    m_watch->start();
}

double timer::get_seconds() {
    return m_watch->get_current_seconds();
}

