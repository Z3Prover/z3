/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    theory_dense_diff_logic.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-05-16.

Revision History:

--*/
#include "smt/theory_dense_diff_logic_def.h"

namespace smt {
    template class theory_dense_diff_logic<mi_ext>;
    template class theory_dense_diff_logic<i_ext>;
    template class theory_dense_diff_logic<smi_ext>;
    template class theory_dense_diff_logic<si_ext>;
};
