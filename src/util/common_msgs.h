/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    common_msgs.h

Abstract:

    Common messages used in Z3.

Author:

    Leonardo (leonardo) 2012-10-25

Notes:

--*/
#ifndef COMMON_MSGS_H_
#define COMMON_MSGS_H_

class common_msgs {
public:
    static char const * g_canceled_msg;
    static char const * g_max_memory_msg;
    static char const * g_max_scopes_msg;
    static char const * g_max_steps_msg;
    static char const * g_max_frames_msg;
    static char const * g_no_proofs_msg;
    static char const * g_max_resource_msg;
};

#define Z3_CANCELED_MSG      common_msgs::g_canceled_msg
#define Z3_MAX_MEMORY_MSG    common_msgs::g_max_memory_msg
#define Z3_MAX_SCOPES_MSG    common_msgs::g_max_scopes_msg
#define Z3_MAX_STEPS_MSG     common_msgs::g_max_steps_msg
#define Z3_MAX_FRAMES_MSG    common_msgs::g_max_frames_msg
#define Z3_NO_PROOF_GEN_MSG  common_msgs::g_no_proofs_msg
#define Z3_MAX_RESOURCE_MSG  common_msgs::g_max_resource_msg

#endif
