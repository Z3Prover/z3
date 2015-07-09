/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    der_tactic.h

Abstract:

    DER tactic

Author:

    Leonardo de Moura (leonardo) 2012-10-20

--*/
#ifndef DER_TACTIC_H_
#define DER_TACTIC_H_

class ast_manager;
class tactic;

tactic * mk_der_tactic(ast_manager & m);

/*
  ADD_TACTIC("der", "destructive equality resolution.", "mk_der_tactic(m)")
*/

#endif /* DER_TACTIC_H_ */
