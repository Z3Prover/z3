/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    random.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2007-08-24.

Revision History:

--*/

#include"util.h"
#include"trace.h"

static void tst1() {
    random_gen r(0);
    TRACE("random", 
          for (unsigned i = 0; i < 1000; i++) {
              tout << r() << "\n";
          });
}

void tst_random() {
    tst1();
}


