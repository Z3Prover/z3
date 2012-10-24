/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    st2tactic.h

Abstract:

    Temporary adapter that converts a assertion_set_strategy into a tactic.

Author:

    Leonardo (leonardo) 2012-02-19

Notes:

--*/
#ifndef _ST2TACTIC_H_
#define _ST2TACTIC_H_

class tactic;
class assertion_set_strategy;

tactic * st2tactic(assertion_set_strategy * st);

#endif
