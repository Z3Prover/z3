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


typedef interpolation_options_struct *interpolation_options;

void iz3interpolate(scoped_ptr<ast_manager> &_m_manager,
		    ast *proof,
		    const ptr_vector<ast> &cnsts,
		    const ::vector<int> &parents,
		    ptr_vector<ast> &interps,
		    const ptr_vector<ast> theory,
		    interpolation_options_struct * options = 0);

#endif
