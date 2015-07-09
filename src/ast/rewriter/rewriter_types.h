/*++
Copyright (c) 2007 Microsoft Corporation

Module Name:

    rewriter_types.h

Abstract:

    Lean and mean rewriter

Author:

    Leonardo (leonardo) 2011-04-10

Notes:

--*/
#ifndef REWRITER_TYPES_H_
#define REWRITER_TYPES_H_

#include"z3_exception.h"
#include"common_msgs.h"

/**
   \brief Builtin rewrite result status
*/
enum br_status {
    BR_REWRITE1,               // rewrite the result (bounded by depth 1)
    BR_REWRITE2,               // rewrite the result (bounded by depth 2)
    BR_REWRITE3,               // rewrite the result (bounded by depth 3)
    BR_REWRITE_FULL,           // rewrite the result unbounded
    BR_DONE,                   // done, the result is simplified
    BR_FAILED                  // no builtin rewrite is available
};

#define RW_UNBOUNDED_DEPTH 3
inline br_status unsigned2br_status(unsigned u) {
    br_status r = u >= RW_UNBOUNDED_DEPTH ? BR_REWRITE_FULL : static_cast<br_status>(u);
    SASSERT((u == 0) == (r == BR_REWRITE1));
    SASSERT((u == 1) == (r == BR_REWRITE2));
    SASSERT((u == 2) == (r == BR_REWRITE3));
    SASSERT((u >= 3) == (r == BR_REWRITE_FULL));
    return r;
}

class rewriter_exception : public default_exception {
public:                                                
    rewriter_exception(char const * msg):default_exception(msg) {}
};

#endif
