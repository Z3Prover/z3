/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

   iz3interp.h

Abstract:

   Interpolation based on proof translation.

Author:

    Ken McMillan (kenmcmil)

Revision History:

--*/

#ifndef IZ3_INTERP_H
#define IZ3_INTERP_H

#include "iz3hash.h"

struct interpolation_options_struct {
  stl_ext::hash_map<std::string,std::string> map;
};

/** This object is thrown if a tree interpolation problem is mal-formed */
struct iz3_bad_tree {
};

/** This object is thrown when iz3 fails due to an incompleteness in
    the secondary solver. */
struct iz3_incompleteness {
};

typedef interpolation_options_struct *interpolation_options;

void iz3interpolate(ast_manager &_m_manager,
		    ast *proof,
		    const ptr_vector<ast> &cnsts,
		    const ::vector<int> &parents,
		    ptr_vector<ast> &interps,
		    const ptr_vector<ast> &theory,
		    interpolation_options_struct * options = 0);

void iz3interpolate(ast_manager &_m_manager,
		    ast *proof,
		    const ptr_vector<ast> &cnsts,
		    ast *tree,
		    ptr_vector<ast> &interps,
		    interpolation_options_struct * options);

#endif
