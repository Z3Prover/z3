/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    theory_arith.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-04-22.

Revision History:

--*/

#include "smt/theory_arith_def.h"

namespace smt {

    template class theory_arith<mi_ext>;
    template class theory_arith<i_ext>;
    // template class theory_arith<si_ext>;
    // template class theory_arith<smi_ext>;

    template class smt::theory_arith<inf_ext>;    
};
