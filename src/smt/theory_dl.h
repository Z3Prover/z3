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
#ifndef THEORY_DL_H_
#define THEORY_DL_H_


namespace smt {

    theory* mk_theory_dl(ast_manager& m);

};

#endif /* THEORY_DL_H_ */

