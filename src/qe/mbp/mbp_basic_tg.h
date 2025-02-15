/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    mbp_basic_tg.h

Abstract:

    Apply rules for model based projection for basic types, on a term graph

Author:

    Hari Govind V K (hgvk94) 2023-03-07

Revision History:

--*/
#pragma once

#include "qe/mbp/mbp_qel_util.h"
#include "qe/mbp/mbp_term_graph.h"
#include "qe/mbp/mbp_tg_plugins.h"
#include "util/obj_hashtable.h"

class mbp_basic_tg : public mbp_tg_plugin {
    struct impl;
    impl *m_impl;

public:
    mbp_basic_tg(ast_manager &man, mbp::term_graph &tg, model &mdl,
                 obj_hashtable<app> &vars_set, expr_sparse_mark &seen);
    // iterate through all terms in m_tg and apply all basic MBP rules once
    // returns true if any rules were applied
    bool apply() override;
    ~mbp_basic_tg() override;
    void use_model() override;
    void get_new_vars(app_ref_vector *&t) override;
    family_id get_family_id() const override;
};
