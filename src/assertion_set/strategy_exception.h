/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    strategy_exception.h

Abstract:

    Strategy exception

Author:

    Leonardo (leonardo) 2011-05-02

Notes:

--*/
#ifndef _STRATEGY_EXCEPTION_H_
#define _STRATEGY_EXCEPTION_H_

#include"z3_exception.h"

class strategy_exception : public z3_exception {
public:
    static char const * g_ste_canceled_msg;
    static char const * g_ste_max_memory_msg;
    static char const * g_ste_max_scopes_msg;
    static char const * g_ste_max_steps_msg;
    static char const * g_ste_max_frames_msg;
    static char const * g_ste_no_proofs_msg;
protected:
    char const * m_msg;
public:
    strategy_exception(char const * msg):m_msg(msg) {}
    virtual ~strategy_exception() {}
    virtual char const * msg() const { return m_msg; }
};

#define STE_CANCELED_MSG      strategy_exception::g_ste_canceled_msg
#define STE_MAX_MEMORY_MSG    strategy_exception::g_ste_max_memory_msg
#define STE_MAX_SCOPES_MSG    strategy_exception::g_ste_max_scopes_msg
#define STE_MAX_STEPS_MSG     strategy_exception::g_ste_max_steps_msg
#define STE_MAX_FRAMES_MSG    strategy_exception::g_ste_max_frames_msg
#define STE_NO_PROOF_GEN_MSG  strategy_exception::g_ste_no_proofs_msg

#define MK_ST_EXCEPTION(NAME)                           \
class NAME : public strategy_exception {                \
public:                                                 \
    NAME(char const * msg):strategy_exception(msg) {}   \
}

#endif
