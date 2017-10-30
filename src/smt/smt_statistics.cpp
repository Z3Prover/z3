/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_statistics.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-02-21.

Revision History:

--*/
#include<string.h>
#include "smt/smt_statistics.h"

namespace smt {

    void statistics::reset() {
        memset(this, 0, sizeof(statistics));
    }

};

