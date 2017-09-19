/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    sat_par.h

Abstract:

    Utilities for parallel SAT solving.

Author:

    Nikolaj Bjorner (nbjorner) 2017-1-29.

Revision History:

--*/
#ifndef SAT_PAR_H_
#define SAT_PAR_H_

#include "sat/sat_types.h"
#include "util/hashtable.h"
#include "util/map.h"

namespace sat {

    class par {
        typedef hashtable<unsigned, u_hash, u_eq> index_set;
        literal_vector m_units;
        index_set      m_unit_set;
    public:
        par();
        void exchange(literal_vector const& in, unsigned& limit, literal_vector& out);
    };

};

#endif
