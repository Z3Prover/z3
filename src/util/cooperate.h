/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    cooperate.h

Abstract:

    Cooperation support

Author:

    Leonardo (leonardo) 2011-05-17

Notes:

--*/
#pragma once

#ifndef SINGLE_THREAD

class cooperation_ctx {
    static bool g_cooperate;
public:
    static bool enabled() { return g_cooperate; }
    static void checkpoint(char const * task);
};

inline void cooperate(char const * task) {
    if (cooperation_ctx::enabled()) cooperation_ctx::checkpoint(task);
}

void initialize_cooperate();
void finalize_cooperate();

/*
  ADD_INITIALIZER('initialize_cooperate();')
  ADD_FINALIZER('finalize_cooperate();')
*/

#else
inline void cooperate(char const *) {}
#endif
