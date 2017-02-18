/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    api_goal.h

Abstract:
    API for creating goals
    
Author:

    Leonardo de Moura (leonardo) 2012-03-06.

Revision History:

--*/
#ifndef API_GOAL_H_
#define API_GOAL_H_

#include"api_util.h"
#include"goal.h"

struct Z3_goal_ref : public api::object {
    goal_ref m_goal;
    Z3_goal_ref(api::context& c) : api::object(c) {}
    virtual ~Z3_goal_ref() {}
};

inline Z3_goal_ref * to_goal(Z3_goal g) { return reinterpret_cast<Z3_goal_ref *>(g); }
inline Z3_goal of_goal(Z3_goal_ref * g) { return reinterpret_cast<Z3_goal>(g); }
inline goal_ref to_goal_ref(Z3_goal g) { return g == 0 ? goal_ref() : to_goal(g)->m_goal; }

#endif
