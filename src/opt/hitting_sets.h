/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    hitting_sets.h

Abstract:
   
    Hitting set approximations.

Author:

    Nikolaj Bjorner (nbjorner) 2014-06-06

Notes:

--*/
#ifndef _HITTING_SETS_H_
#define _HITTING_SETS_H_

#include "rational.h"
#include "statistics.h"

namespace opt {

    class hitting_sets {
        struct imp;
        imp* m_imp;
    public:        
        hitting_sets();
        ~hitting_sets();
        void add_weight(rational const& w);
        void add_set(unsigned sz, unsigned const* elems);
        bool compute_lower();
        bool compute_upper();
        rational get_lower();
        rational get_upper();        
        void set_cancel(bool f);
        void collect_statistics(::statistics& st) const;
        void reset();
    };


};

#endif
