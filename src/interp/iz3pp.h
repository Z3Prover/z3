/*++
  Copyright (c) 2013 Microsoft Corporation

  Module Name:

  iz3pp.cpp

  Abstract:

  Pretty-print interpolation problems

  Author:

  Ken McMillan (kenmcmil)

  Revision History:

  --*/

#ifndef IZ3_PP_H
#define IZ3_PP_H

#include "iz3mgr.h"

/** Exception thrown in case of mal-formed tree interpoloation
    specification */

struct iz3pp_bad_tree: public iz3_exception {
    iz3pp_bad_tree(): iz3_exception("iz3pp_bad_tree") {}
};

void iz3pp(ast_manager &m,
	   const ptr_vector<expr> &cnsts_vec,
	   expr *tree,
	   std::ostream& out);
#endif
