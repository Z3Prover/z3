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
#ifndef COOPERATE_H_
#define COOPERATE_H_

class cooperation_section;

class cooperation_ctx {
    friend class cooperation_section;
    static bool g_cooperate;
public:
    static bool enabled() { return g_cooperate; }
    static void checkpoint(char const * task);
};

inline void cooperate(char const * task) {
    if (cooperation_ctx::enabled()) cooperation_ctx::checkpoint(task);
}

// must be declared before "#pragma parallel" to enable cooperation 
class cooperation_section {
public:
    cooperation_section();
    ~cooperation_section();
};

// must be first declaration inside "#pragma parallel for"
class init_task {
public:
    init_task(char const * task);
    ~init_task();
};

#endif
