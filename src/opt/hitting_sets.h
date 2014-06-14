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
#include "lbool.h"

namespace opt {

    class hitting_sets {
        struct imp;
        imp* m_imp;
    public:        
        hitting_sets();
        ~hitting_sets();
        void add_weight(rational const& w);
        void add_exists_true(unsigned sz, unsigned const* elems);
        void add_exists_false(unsigned sz, unsigned const* elems);
        lbool compute_lower();
        lbool compute_upper();
        void set_upper(rational const& r);
        rational get_lower();
        rational get_upper();        
        bool get_value(unsigned idx);
        void set_cancel(bool f);
        void collect_statistics(::statistics& st) const;
        void reset();
    };


};

#endif
