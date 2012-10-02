/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    sat_extension.h

Abstract:

    An abstract class for SAT extensions.

Author:

    Leonardo de Moura (leonardo) 2011-05-21.

Revision History:

--*/
#ifndef _SAT_EXTENSION_H_
#define _SAT_EXTENSION_H_

#include"sat_types.h"
#include"params.h"

namespace sat {

    enum check_result {
        CR_DONE, CR_CONTINUE, CR_GIVEUP
    };

    class extension {
    public:
        virtual void propagate(literal l, ext_constraint_idx idx, bool & keep) = 0;
        virtual void get_antecedents(literal l, ext_justification_idx idx, literal_vector & r) = 0;
        virtual void asserted(literal l) = 0;
        virtual check_result check() = 0;
        virtual void push() = 0;
        virtual void pop(unsigned n) = 0;
        virtual void simplify() = 0;
        virtual void clauses_modifed() = 0;
        virtual lbool get_phase(bool_var v) = 0;
    };

};

#endif
