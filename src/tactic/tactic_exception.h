/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    tactic_exception.h

Abstract:

    Tactic exception object.

Author:

    Leonardo (leonardo) 2012-08-15

Notes:

--*/
#pragma once

#include "util/z3_exception.h"
#include "util/common_msgs.h"

class tactic_exception : public z3_exception {
protected:
    std::string m_msg;
public:
    tactic_exception(std::string && msg) : m_msg(std::move(msg)) {}
    ~tactic_exception() override {}
    char const * msg() const override { return m_msg.c_str(); }
};

#define TACTIC_CANCELED_MSG      Z3_CANCELED_MSG
#define TACTIC_MAX_MEMORY_MSG    Z3_MAX_MEMORY_MSG
#define TACTIC_MAX_SCOPES_MSG    Z3_MAX_SCOPES_MSG
#define TACTIC_MAX_STEPS_MSG     Z3_MAX_STEPS_MSG
#define TACTIC_MAX_FRAMES_MSG    Z3_MAX_FRAMES_MSG
#define TACTIC_NO_PROOF_GEN_MSG  Z3_NO_PROOF_GEN_MSG

