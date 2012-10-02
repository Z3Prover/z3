/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    tactic_exception.h

Abstract:

    Tactic expection object.

Author:

    Leonardo (leonardo) 2012-08-15

Notes:

--*/
#ifndef _TACTIC_EXCEPTION_H_
#define _TACTIC_EXCEPTION_H_

#include"z3_exception.h"

class tactic_exception : public z3_exception {
public:
    static char const * g_tactic_canceled_msg;
    static char const * g_tactic_max_memory_msg;
    static char const * g_tactic_max_scopes_msg;
    static char const * g_tactic_max_steps_msg;
    static char const * g_tactic_max_frames_msg;
    static char const * g_tactic_no_proofs_msg;
protected:
    std::string m_msg;
public:
    tactic_exception(char const * msg):m_msg(msg) {}
    virtual ~tactic_exception() {}
    virtual char const * msg() const { return m_msg.c_str(); }
};

#define TACTIC_CANCELED_MSG      tactic_exception::g_tactic_canceled_msg
#define TACTIC_MAX_MEMORY_MSG    tactic_exception::g_tactic_max_memory_msg
#define TACTIC_MAX_SCOPES_MSG    tactic_exception::g_tactic_max_scopes_msg
#define TACTIC_MAX_STEPS_MSG     tactic_exception::g_tactic_max_steps_msg
#define TACTIC_MAX_FRAMES_MSG    tactic_exception::g_tactic_max_frames_msg
#define TACTIC_NO_PROOF_GEN_MSG  tactic_exception::g_tactic_no_proofs_msg

#endif
