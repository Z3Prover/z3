/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    lbool.h

Abstract:

    Lifted boolean

Author:

    Leonardo de Moura (leonardo) 2008-02-08.

Revision History:

--*/
#ifndef _LBOOL_H_
#define _LBOOL_H_

#include"util.h"

typedef enum { l_false = -1, l_undef, l_true } lbool;

inline lbool operator~(lbool lb) {
    return static_cast<lbool>(-static_cast<int>(lb));
}

inline lbool to_lbool(bool b) {
    return static_cast<lbool>(static_cast<int>(b)*2-1);
}

std::ostream & operator<<(std::ostream & out, lbool b);

/**
   \brief Convert l_true -> satisfiable, l_false -> unsatisfiable, and l_undef -> unknown.
*/
char const * to_sat_str(lbool l);

#endif /* _LBOOL_H_ */

