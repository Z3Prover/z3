/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    bvarray2ufbvarray2uf_tactic.h

Abstract:

    Tactic that rewrites bit-vector arrays into bit-vector
    (uninterpreted) functions.

Author:

    Christoph (cwinter) 2015-11-04

Notes:

--*/
#pragma once

#include "util/params.h"
class ast_manager;
class tactic;

tactic * mk_bvarray2uf_tactic(ast_manager & m, params_ref const & p = params_ref());
/*
    ADD_TACTIC("bvarray2uf", "Rewrite bit-vector arrays into bit-vector (uninterpreted) functions.", "mk_bvarray2uf_tactic(m, p)")
*/


