/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    num_occurs_goal.h

Abstract:


Author:

    Leonardo de Moura (leonardo) 2012-10-20.

Revision History:

--*/
#ifndef _NUM_OCCURS_GOAL_H_
#define _NUM_OCCURS_GOAL_H_

#include"num_occurs.h"

class goal;

class num_occurs_goal : public num_occurs { 
public:
    num_occurs_goal(bool ignore_ref_count1 = false, bool ignore_quantifiers = false):
        num_occurs(ignore_ref_count1, ignore_quantifiers) {
    }

    void operator()(goal const & s);
};


#endif
