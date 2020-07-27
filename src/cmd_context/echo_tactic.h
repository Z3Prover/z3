/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    echo_tactic.h

Abstract:

    Tactic and probe for dumping data.

Author:

    Leonardo (leonardo) 2012-10-20

Notes:

--*/
#pragma once

class cmd_context;
class tactic;
class probe;

tactic * mk_echo_tactic(cmd_context & ctx, char const * msg, bool newline = true);
// Display the value returned by p in the diagnostic_stream
tactic * mk_probe_value_tactic(cmd_context & ctx, char const * msg, probe * p, bool newline = true);

