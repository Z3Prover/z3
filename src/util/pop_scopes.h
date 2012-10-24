/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    pop_scopes.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-06-02.

Revision History:

--*/
#ifndef _POP_SCOPES_H_
#define _POP_SCOPES_H_

#define POP_SCOPES(_num_scopes, _lim, _trail, _action)          \
    if (_num_scopes > 0)                                        \
    {                                                           \
        unsigned scope_lvl = _lim.size();                       \
        unsigned new_lvl   = scope_lvl - _num_scopes;           \
        unsigned curr_size = _trail.size();                     \
        unsigned old_size  = _lim[new_lvl];                     \
        for (unsigned i = curr_size-1; i >= old_size && i != static_cast<unsigned>(-1); --i) { \
            _action;                                            \
        }                                                       \
        _trail.shrink(old_size);                                \
        _lim.shrink(new_lvl);                                   \
    }

#endif /* _POP_SCOPES_H_ */

