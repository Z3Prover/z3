/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    elim_distinct.h

Abstract:

    Replace one distinct(t0, ..., tn) with (t0 = 0 and ... and tn = n)
    when the sort of t0...tn is uninterpreted.

Author:

    Leonardo de Moura (leonardo) 2011-04-28

Revision History:

--*/
#ifndef _ELIM_DISTINCT_H_
#define _ELIM_DISTINCT_H_

#include"assertion_set.h"

class model_converter;
class ast_manager;
class assertion_set;

class elim_distinct_exception : public default_exception {
public:
    elim_distinct_exception(char const * msg):default_exception(msg) {}
};

class elim_distinct {
    struct imp;
    imp *  m_imp;
public:
    elim_distinct(ast_manager & m);
    ~elim_distinct();

    /**
       \brief It throws an elim_distinct_exception if the strategy failed.
       If d == 0, then search for the biggest distinct(t0, ..., tn) in the assertion set.
       if d != 0, then succeed only if d is in the assertion set.
    */
    model_converter * operator()(assertion_set & s, app * d);

    void cancel();

    void reset();
    void cleanup();
};

#endif
