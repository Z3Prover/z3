/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    api_stats.h

Abstract:
    API for Z3 statistics
    
Author:

    Leonardo de Moura (leonardo) 2012-03-07.

Revision History:

--*/
#ifndef API_STATS_H_
#define API_STATS_H_

#include"api_util.h"
#include"statistics.h"

struct Z3_stats_ref : public api::object {
    statistics m_stats;
    Z3_stats_ref(api::context& c): api::object(c) {}
    virtual ~Z3_stats_ref() {}
};

inline Z3_stats_ref * to_stats(Z3_stats s) { return reinterpret_cast<Z3_stats_ref *>(s); }
inline Z3_stats of_stats(Z3_stats_ref * s) { return reinterpret_cast<Z3_stats>(s); }
inline statistics & to_stats_ref(Z3_stats s) { return to_stats(s)->m_stats; }

#endif
