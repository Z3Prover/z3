/*++
Copyright (c) 2018 Arie Gurfinkel

Module Name:

    spacer_mbc.h

Abstract:

  Model-Based Cartesian Decomposition

Author:

    Arie Gurfinkel

Revision History:

--*/

#pragma once

#include "ast/ast.h"
#include "util/obj_hashtable.h"
#include "model/model.h"

namespace spacer {

class mbc {
    ast_manager &m;
public:
    mbc(ast_manager &m);


    typedef obj_map<func_decl, unsigned> partition_map;

    /**
       \Brief Model Based Cartesian projection of lits
     */
    void operator()(const partition_map &pmap, expr_ref_vector &lits, model &mdl,
                    vector<expr_ref_vector> &res);
};

}
