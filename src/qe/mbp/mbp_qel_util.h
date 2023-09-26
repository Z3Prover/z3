/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    mbp_qel_util.h

Abstract:

    Utility methods for mbp_qel

Author:

    Hari Govind V K (hgvk94) 2023-03-07

Revision History:

--*/

#pragma once

#include "ast/array_decl_plugin.h"
#include "ast/ast.h"
#include "ast/ast_pp.h"
#include "ast/ast_util.h"
#include "ast/for_each_expr.h"
#include "ast/pp.h"

// check if e contains any apps from vars
// if fid and dk are not null, check if the variable is of desired sort
bool contains_vars(expr *e, obj_hashtable<app> const &vars, ast_manager &man,
                   family_id fid = null_family_id,
                   decl_kind dk = null_decl_kind);

app_ref new_var(sort *s, ast_manager &m);

// Return all uninterpreted constants of \p q
void collect_uninterp_consts(expr *e, obj_hashtable<app> &out);
// collect all uninterpreted consts used as array indices or values
void collect_selstore_vars(expr *fml, obj_hashtable<app> &vars,
                           ast_manager &man);
