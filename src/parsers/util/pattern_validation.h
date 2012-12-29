/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    pattern_validation.h

Abstract:

    Code for checking whether a pattern is valid or not.

Author:

    Leonardo de Moura (leonardo) 2006-12-08.

Revision History:

--*/
#ifndef _PATTERN_VALIDATION_H_
#define _PATTERN_VALIDATION_H_

#include"ast.h"
#include"uint_set.h"
#include"vector.h"

class pattern_validator {
    family_id          m_bfid;
    family_id          m_lfid;

    bool process(uint_set & found_vars, unsigned num_bindings, unsigned num_new_bindings, expr * n);

public:
    pattern_validator(ast_manager const & m):
        m_bfid(m.get_basic_family_id()),
        m_lfid(m.get_label_family_id()) {
    }

    bool operator()(unsigned num_bindings, unsigned num_new_bindings, expr * n);
    bool operator()(unsigned num_new_bindings, expr * n) { return operator()(UINT_MAX, num_new_bindings, n); }
};

#endif /* _PATTERN_VALIDATION_H_ */

