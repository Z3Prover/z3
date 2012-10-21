/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    der_tactic.h

Abstract:

    DER tactic

Author:

    Leonardo de Moura (leonardo) 2012-10-20

--*/
#ifndef _DER_TACTIC_H_
#define _DER_TACTIC_H_

class ast_manager;
class tactic;

tactic * mk_der_tactic(ast_manager & m);

#endif /* _DER_TACTIC_H_ */
