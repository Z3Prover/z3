/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    goal_num_occurs.h

Abstract:


Author:

    Leonardo de Moura (leonardo) 2012-10-20.

Revision History:

--*/
#ifndef GOAL_NUM_OCCURS_H_
#define GOAL_NUM_OCCURS_H_

#include"num_occurs.h"

class goal;

class goal_num_occurs : public num_occurs { 
public:
    goal_num_occurs(bool ignore_ref_count1 = false, bool ignore_quantifiers = false):
        num_occurs(ignore_ref_count1, ignore_quantifiers) {
    }

    void operator()(goal const & s);
};


#endif
