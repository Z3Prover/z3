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

bool iz3check(iz3mgr &mgr,
	      solver *s,
	      std::ostream &err,
	      const std::vector<iz3mgr::ast> &cnsts,
	      const std::vector<int> &parents,
	      const std::vector<iz3mgr::ast> &interps,
	      const ptr_vector<iz3mgr::ast> &theory);

#endif
