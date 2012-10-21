/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    num_occurs_assertion_set.h

Abstract:

    TODO: delete

Author:

    Leonardo de Moura (leonardo) 2012-10-20.

Revision History:

--*/
#ifndef _NUM_OCCURS_AS_H_
#define _NUM_OCCURS_AS_H_

#include"num_occurs.h"

class assertion_set;

/**
   \brief Functor for computing the number of occurrences of each sub-expression in a expression F.
*/
class num_occurs_as : public num_occurs { 
public:
    num_occurs_as(bool ignore_ref_count1 = false, bool ignore_quantifiers = false):
        num_occurs(ignore_ref_count1, ignore_quantifiers) {
    }

    void operator()(assertion_set const & s); // TODO delete
};

#endif
