/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    sat_iff3_finder.h

Abstract:

    Find constraints of the form   x = l1 = l2
    That is, search for clauses of the form
      ~x \/ l1  \/ ~l2
      ~x \/ ~l1 \/ l2
       x \/ l1  \/ l2
       x \/ ~l1 \/ ~l2
       
    The basic idea is to sort the watch lists.
    
    This information can be used to propagate equivalences
    during probing (and search).

Author:

    Leonardo de Moura (leonardo) 2011-06-04.

Revision History:

--*/
#ifndef _SAT_IFF3_FINDER_H_
#define _SAT_IFF3_FINDER_H_

#include"sat_types.h"

namespace sat {
    
    class iff3_finder {
        solver & s;
        void sort_watches();
        void mk_eq(literal l1, literal l2);
    public:
        iff3_finder(solver & s);
        
        void operator()();
    };

};

#endif
