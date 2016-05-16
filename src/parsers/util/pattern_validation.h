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
#ifndef PATTERN_VALIDATION_H_
#define PATTERN_VALIDATION_H_

#include"ast.h"
#include"uint_set.h"
#include"vector.h"

class pattern_validator {
    family_id          m_bfid;
    family_id          m_lfid;

    bool process(uint_set & found_vars, unsigned num_bindings, unsigned num_new_bindings, expr * n, unsigned line, unsigned pos);

public:
    pattern_validator(ast_manager const & m):
        m_bfid(m.get_basic_family_id()),
        m_lfid(m.get_label_family_id()) {
    }

    bool operator()(unsigned num_bindings, unsigned num_new_bindings, expr * n, unsigned line, unsigned pos);
    bool operator()(unsigned num_new_bindings, expr * n, unsigned line, unsigned pos) { return operator()(UINT_MAX, num_new_bindings, n, line, pos); }
};

#endif /* PATTERN_VALIDATION_H_ */

