/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    theory_dl.h

Abstract:

    Basic theory solver for DL finite domains.

Author:

    Nikolaj Bjorner (nbjorner) 2011-10-3

Revision History:

--*/
#pragma once


namespace smt {

    theory* mk_theory_dl(context& ctx);

};


