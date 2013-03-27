/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

   iz3checker.h

Abstract:

   check correctness of an interpolant

Author:

    Ken McMillan (kenmcmil)

Revision History:

--*/

#ifndef IZ3_CHECKER_H
#define IZ3_CHECKER_H

#include "iz3mgr.h"
#include "solver.h"

bool iz3check(ast_manager &_m_manager,
	      solver *s,
	      std::ostream &err,
	      const ptr_vector<ast> &cnsts,
	      const ::vector<int> &parents,
	      const ptr_vector<ast> &interps,
	      const ptr_vector<ast> &theory);

bool iz3check(ast_manager &_m_manager,
	      solver *s,
	      std::ostream &err,
	      const ptr_vector<ast> &cnsts,
	      ast *tree,
	      const ptr_vector<ast> &interps);

#endif
