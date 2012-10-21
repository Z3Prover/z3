/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    goal_shared_occs.h

Abstract:

    Functor for computing the set of shared occurrences in a goal.

Author:

    Leonardo de Moura (leonardo) 2011-12-28

Revision History:

--*/
#ifndef _GOAL_SHARED_OCCS_H_
#define _GOAL_SHARED_OCCS_H_

#include"goal.h"
#include"shared_occs.h"

/**
   \brief Functor for computing the set of shared occurrences in a goal.
   
   It is essentially a wrapper for shared_occs functor.
*/
class goal_shared_occs {
    shared_occs m_occs;
public:
    goal_shared_occs(ast_manager & m, bool track_atomic = false, bool visit_quantifiers = true, bool visit_patterns = false):
        m_occs(m, track_atomic, visit_quantifiers, visit_patterns) {
    }
    void operator()(goal const & s);
    bool is_shared(expr * t) { return m_occs.is_shared(t); }
    unsigned num_shared() const { return m_occs.num_shared(); }
    void reset() { return m_occs.reset(); }
    void cleanup() { return m_occs.cleanup(); }
    void display(std::ostream & out, ast_manager & m) const { m_occs.display(out, m); }
};


#endif
